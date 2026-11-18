open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)

let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool = 
  begin match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  (*more complex*)
  | TRef rt1, TRef rt2 -> subtype_ref c rt1 rt2
  | TNullRef rt1, TNullRef rt2 -> subtype_ref c rt1 rt2
  | TRef rt1, TNullRef rt2 -> subtype_ref c rt1 rt2 (*have to do both cases?*)
  | _ -> false
  end

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  begin match t1, t2 with
  | RString, RString -> true

  | RArray rt1, RArray rt2 -> rt1 = rt2

  | RStruct rt1, RStruct rt2 -> if (rt1 = rt2) then true else (subtype_struct_el c rt1 rt2)

  | RFun (args1, return1), RFun (args2, return2) -> 
    (subtype_ret_ty c return1 return2) && (*same return type*)
    (List.length args1 = List.length args2) && (* same number of args*)
    (List.fold_left2 (fun ret arg1 arg2 -> ret && (subtype c arg2 arg1)) true args1 args2) (*check each arg for same type*)
  
  | _ -> false
  end

and subtype_ret_ty (c: Tctxt.t) (t1: Ast.ret_ty) (t2: Ast.ret_ty): bool =
  begin match t1, t2 with
  | RetVoid, RetVoid -> true
  | RetVal rt1, RetVal rt2 -> subtype c rt1 rt2
  | _ -> false
  end

and subtype_struct_el (c: Tctxt.t) (id1: Ast.id) (id2: Ast.id): bool = (*maybe wrong*)
  begin match Tctxt.lookup_struct_option id1 c, Tctxt.lookup_struct_option id2 c with
  | Some st1, Some st2 ->  
    let rec aux (fl1: field list) (fl2: field list): bool = 
      begin match fl1, fl2 with
      | x::xs, y::ys -> if (y.ftyp = x.ftyp) && (x.fieldName = y.fieldName) then (aux xs ys) else false
      | [], [] -> true
      | _, [] -> true
      | [], _ -> false
      end in 
        aux st1 st2 
  | _ -> false
  end

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  begin match t with
  | TInt | TBool -> ()
  | TRef rty | TNullRef rty -> typecheck_rty l tc rty
  end

and typecheck_rty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit = 
  let func_ty_args_check = (fun _ ty_s -> typecheck_ty l tc ty_s) in 
    begin match t with
    | RString -> ()
    | RArray ty -> typecheck_ty l tc ty

    | RStruct id -> 
      let _ = 
        begin match (Tctxt.lookup_struct_option id tc) with
        | Some (list) -> list 
        | _ -> type_error l id end in ()
        (* List.fold_left (fun _ field_s -> typecheck_ty l tc field_s.ftyp) () struct_list *)

    | RFun (arg_tys, RetVal ty) -> List.fold_left func_ty_args_check () arg_tys; typecheck_ty l tc ty

    | RFun (arg_tys, RetVoid) -> List.fold_left func_ty_args_check () arg_tys
    end

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  begin match e.elt with
  | CNull rty -> Ast.TNullRef rty (*idk if Tref or Tnullref*)
  | CBool _ -> Ast.TBool
  | CInt _ -> Ast.TInt
  | CStr _ -> TRef RString (*idk if Tref or Tnullref*)
  | Id id -> 
      begin match Tctxt.lookup_option id c with
      | Some x -> x
      | None -> type_error e ("id:" ^ id ^ " is not existing")
      end

  | CArr (ty1, exp_list) -> typecheck_ty e c ty1; 
    List.fold_left (fun _ x -> if Bool.not (subtype c (typecheck_exp c x) ty1) then (type_error e "type of the array not the same es the value")) () exp_list; 
    Ast.TRef (RArray ty1)

  | NewArr (ty, exp1, id, exp2) ->
    (* Printf.printf("ID: %s\n") *)
    begin match (Tctxt.lookup_local_option id c) with
    | Some _ -> (type_error e "variable already in local")
    | None -> ()
    end; 

    if (typecheck_exp c exp1) != Ast.TInt then (type_error e "exp1 is not a Int");
    begin match typecheck_exp (Tctxt.add_local c id Ast.TInt) exp2 with
    | ty_s -> (if (subtype c ty ty_s) then (TRef (RArray ty_s)) else (type_error e "type error")) (*maybe wrong*)
    end

  | Index (array, index) -> 
    if ( (typecheck_exp c index) != Ast.TInt) then (type_error e "Index is not Int"); (*check if the index is a Int type*)
      begin match typecheck_exp c array with 
      | TRef (RArray ty) -> ty 
      | _ -> (type_error e "Can not acces a non array element") 
      end

  | Length exp1 -> 
    let ty_exp1 = typecheck_exp c exp1 in 
      begin match ty_exp1 with 
      | TRef (RArray _)  -> Ast.TInt 
      | _ -> type_error (no_loc e) "Length needs an array"
      end

  | CStruct (id1, list) -> 
    let list_sort = List.sort (fun (id1, _) (id2, _)  -> String.compare id1 id2) list in 
      let _ = begin match lookup_struct_option id1 c with | Some x -> x | _ -> type_error e "Can not find struct" end in 
        let size_st = List.length (Tctxt.lookup_struct id1 c) in 
          let number_of_assg = List.fold_left (fun count (id, exp) -> 
                              begin match Tctxt.lookup_field_option id1 id c with
                              | Some x -> if (Bool.not (subtype c (typecheck_exp c exp) x)) then (type_error e "ty of the struct is not the same")
                              | None -> (type_error e "Name of the struct var not existing")
                              end; (count + 1)) 0 list_sort in 
        if (size_st = number_of_assg) then TRef (RStruct id1) else type_error e "to much assignments"

  | Proj (exp1, id) -> 
    let list_ty = begin match typecheck_exp c exp1 with
                   | TRef (RStruct id2) -> begin match Tctxt.lookup_struct_option id2 c with 
                                          | Some x -> x 
                                          | None -> type_error e "not found struct with id" end 
                   | _ -> type_error e "No struct found"
                  end in 
    begin match List.find_opt (fun x -> x.fieldName = id) list_ty with
    | Some x -> x.ftyp
    | None -> type_error e "couldn't find id of element"
    end        

  | Call (exp, args_list) -> 
    let args_ty, return_ty = 
    begin match typecheck_exp c exp with 
    | TRef RFun (args_type, ret_type) -> (args_type, ret_type) 
    | TNullRef RFun (args_type, ret_type) -> (args_type, ret_type) 
    | _ -> (type_error (no_loc e) "Have to call a Func") end in 

      if List.length args_list != List.length args_ty then (type_error (no_loc e) "Not the correct number of args"); 
      List.fold_left2 (fun _ x y -> if Bool.not (subtype c (typecheck_exp c y) x) then (type_error e "not the correct arg type") ) () args_ty args_list; 
      begin match return_ty with
      | RetVoid -> type_error e "Void return of the func"
      | RetVal x -> x
      end
      
  | Bop (binop, exp1, exp2) ->
    let check_ty = fun x y -> if Bool.not (subtype c y x) then type_error e "Wrong input type for Binop" in 
    begin match binop with
    | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> 
      check_ty Ast.TInt (typecheck_exp c exp1); check_ty Ast.TInt (typecheck_exp c exp2); Ast.TInt
    | Eq | Neq | Lt | Lte | Gt | Gte -> 
      check_ty Ast.TInt (typecheck_exp c exp1); check_ty Ast.TInt (typecheck_exp c exp2); Ast.TBool
    | And | Or ->
      check_ty Ast.TBool (typecheck_exp c exp1); check_ty Ast.TBool (typecheck_exp c exp2); Ast.TBool
    end

  | Uop (unop, exp) -> 
    let check_ty = fun x y -> if Bool.not (subtype c x y) then type_error (no_loc e) "Wrong input type for Uop" in
      begin match unop with
      | Neg -> check_ty (typecheck_exp c exp) Ast.TInt; Ast.TInt
      | Lognot -> check_ty (typecheck_exp c exp) Ast.TBool; Ast.TBool
      | Bitnot -> check_ty (typecheck_exp c exp) Ast.TInt; Ast.TInt
      end
  end

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statement typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  let rec stmts_list_b (c: Tctxt.t) (stm: Ast.stmt node list) : Tctxt.t * bool =  
    begin match stm with
    | [] -> (c, false)
    | x::[] -> typecheck_stmt c x to_ret
    | x::xs -> let (c2, bool_ret) = typecheck_stmt c x to_ret in 
                  if (bool_ret) then type_error x "to early return" else stmts_list_b c2 xs
    end in 

  begin match s.elt with
  | Assn (exp1, exp2) -> 
      begin match exp1.elt with
      | Id x -> 
        begin match Tctxt.lookup_global_option x tc, Tctxt.lookup_local_option x tc with
        | Some (TRef (RFun _)), None -> type_error s ("Cant ass func " ^  (Astlib.string_of_exp exp1))
        | _ -> ()
        end
      | _ -> ()
      end;
        if Bool.not (subtype tc (typecheck_exp tc exp2) (typecheck_exp tc exp1)) then (type_error s "not the same type");
          (tc, false)

  | Decl (id, exp) ->
    begin match Tctxt.lookup_local_option id tc with
    | Some _ -> type_error s ("id: " ^ id ^ " already declared var")
    | None -> (Tctxt.add_local tc (id) (typecheck_exp tc exp), false)
    end

  | Ret (exp_op) -> 
    begin match exp_op, to_ret with (*check if it is the same or not, maybe wrong*)
    | Some x, RetVal ty -> if subtype tc (typecheck_exp tc x) ty then (tc, true) else type_error s "Return types are not the same"
    | None, RetVoid -> (tc, true)
    | _ -> type_error s "Wrong types"
    end

  | SCall (exp1, exp_list) -> 
      let (args_ty, return_ty) = 
        begin match typecheck_exp tc exp1 with 
        | TRef RFun (args_type, ret_type) -> (args_type, ret_type) 
        | TNullRef RFun (args_type, ret_type) -> (args_type, ret_type) 
        | _ -> (type_error (no_loc s) "Have to scall a Func") 
        end in

          if List.length args_ty != List.length exp_list then (type_error (no_loc s) "Not the correct number of args"); 
          List.fold_left2 (fun _ x y -> 
          if Bool.not (subtype tc (typecheck_exp tc y) x) then (type_error s "Not the correct typ") ) () args_ty exp_list;
          
          begin match return_ty with
          | RetVoid -> (tc, false)
          | RetVal _ -> type_error s "Should return void"
          end

  | If (exp, stmt_list1, stmt_list2) -> 
    if Bool.not (subtype tc (typecheck_exp tc exp) TBool) then (type_error s "is not a bool value");
      let (_, ret_b1) = stmts_list_b tc stmt_list1  in (*only see if it returns or not*)
        let (_, ret_b2) = stmts_list_b tc stmt_list2  in (*only see if it return or not*)
          (tc, ret_b1 && ret_b2)

  | Cast (ty, id, exp, stmt_list1, stmt_list2) -> 
    let ty_ref = begin match typecheck_exp tc exp with
    | TNullRef x -> TRef x
    | _ -> type_error s "not a null ref"
    end in 
    if Bool.not (subtype tc ty_ref (TRef ty)) then (type_error s "error");

    let c1 = begin match Tctxt.lookup_local_option id tc with
      | None -> Tctxt.add_local tc id ty_ref
      | Some _ -> type_error s "already defined variable" 
      end in 
      let (_, ret_b1) = stmts_list_b c1 stmt_list1  in 
        let (_, ret_b2) = stmts_list_b c1 stmt_list2  in 
          (tc, ret_b1 && ret_b2)

  | For (vdecl_list, exp_op, stmt_op, stmt_list) -> 
    let c1 = List.fold_left (fun c_cur x -> let (c_new, _) = typecheck_stmt c_cur (no_loc (Decl x)) to_ret in c_new) tc vdecl_list in 
      begin match exp_op with
      | None -> ()
      | Some x -> if ((typecheck_exp c1 x) != TBool) then (type_error s "is not a bool value")
      end;
      begin match stmt_op with
      | None -> ()
      | Some x -> let _, rest = typecheck_stmt c1 x to_ret in
                   if rest then (type_error s "should not return") else ()
      end; 
      let _ = stmts_list_b c1 stmt_list  in 
        (tc, false)

  | While (exp, stmt_list) ->
    if ((typecheck_exp tc exp) != TBool) then (type_error s "is not a bool value");
      let _ = stmts_list_b tc stmt_list  in 
        (tc, false)

  end


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let c = List.fold_left (fun c1 (x,y) -> Tctxt.add_local c1 y x) tc f.args in 
    let rec check_ret (c1: Tctxt.t) (block: Ast.block) = 
      begin match block with
      | [] -> ()
      | x::[] -> let (_, state) = typecheck_stmt c1 x f.frtyp in 
                if Bool.not state then type_error x ("No return statement")
      | x::xs -> let (c2, state) = typecheck_stmt c1 x f.frtyp in 
                  if state then type_error x "Should not return" else check_ret c2 xs
      end in 
        check_ret c f.body 


(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let c = Tctxt.empty in 
  List.fold_left (fun c1 x -> 
                  begin match x with
                  | Gtdecl node -> 
                    let (id, field_list) = node.elt in
                      begin match Tctxt.lookup_struct_option id c1 with
                      | Some _ -> type_error node "struct already exists"
                      | None -> 
                        (* let field_list_sorted = List.sort (fun x y -> String.compare x.fieldName y.fieldName) field_list in  *)
                        (* let _ = List.fold_left (fun last x -> (if Bool.not (String.equal last x.fieldName) then (type_error node "two fields with the same id")); x.fieldName) "hsadfsfashahashadhahadhaerhgqeghhysdgasdgaggwqg" field_list_sorted in have a extremly unrealistic start name *)
                          Tctxt.add_struct c1 id field_list
                      end
                  | _ -> c1 (*fdecl = function dec and gvdecl global dec*)
                  end) c p 

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let c = List.fold_left (fun c x -> 
                  begin match x with
                  | Gfdecl node -> 
                    let f_decl = node.elt in 
                      let args_ty = List.map (fun (ty1, _) -> ty1) f_decl.args in
                        begin match Tctxt.lookup_global_option f_decl.fname c with
                        | Some _ -> type_error node "function already exists"
                        | None -> Tctxt.add_global c f_decl.fname (TRef (RFun (args_ty, f_decl.frtyp)))
                        end
                  | _ -> c
                  end) tc p in 
                   List.fold_left (fun c1 (func_id, (args_ty, return_ty)) -> 
                                      Tctxt.add_global c1 func_id (TRef (RFun (args_ty, return_ty)))) c builtins (*add global func*)

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t = 
  let c1, global_var = List.fold_left (fun (c, l) x -> 
                  begin match x with
                  | Gvdecl node -> 
                    let g_decl = node.elt in 
                      begin match Tctxt.lookup_global_option g_decl.name c with
                      | Some _ -> type_error node "global already declared"
                      | None -> (Tctxt.add_global c g_decl.name (typecheck_exp c g_decl.init), (g_decl.name, g_decl.init)::l)
                      end
                  | _ -> (c, l)
                  end) (tc, []) p in

    List.fold_left (fun _ (_, x) -> 
                    begin match x.elt with 
                    | Id id -> 
                      begin match (List.assoc_opt id global_var) with
                      | Some _ -> type_error x "global can not be assigned to global"
                      | None -> ()
                      end
                    | _ -> () 
                    end) () global_var; c1

(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p