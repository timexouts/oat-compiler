open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)





let cmp_binop (c: Ctxt.t) (binop:Ast.binop) ((ty1, op1, st1):Ll.ty * Ll.operand * stream) ((ty2, op2, st2): Ll.ty * Ll.operand * stream): Ll.ty * Ll.operand * stream =
  let res_t = gensym "a" in 
    begin match binop with
    | Add -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Add, I64, op1, op2)))])
    | Sub -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Sub, I64, op1, op2)))])
    | Mul -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Mul, I64, op1, op2)))])
    (*compare*)
    | Eq -> (I1, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Icmp (Ll.Eq, I64, op1, op2)))])
    | Neq -> (I1, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Icmp (Ll.Ne, I64, op1, op2)))])
    | Lt -> (I1, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Icmp (Ll.Slt, I64, op1, op2)))])
    | Lte -> (I1, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Icmp (Ll.Sle, I64, op1, op2)))])
    | Gt -> (I1, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Icmp (Ll.Sgt, I64, op1, op2)))])
    | Gte -> (I1, Id res_t, st1 >@ st2>@ [I (res_t, (Ll.Icmp (Ll.Sge, I64, op1, op2)))])
    (*Logic*)
    | And -> (I1, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.And, I1, op1, op2)))])
    | Or -> (I1, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Or, I1, op1, op2)))])
    (*Bitwise*)
    | IAnd -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.And, I64, op1, op2)))])
    | IOr -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Or, I64, op1, op2)))])
    | Shl -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Shl, I64, op1, op2)))])
    | Shr -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Lshr, I64, op1, op2)))]) (*maybe wrong*)
    | Sar -> (I64, Id res_t, st1 >@ st2 >@ [I (res_t, (Ll.Binop (Ll.Ashr, I64, op1, op2)))]) (*maybe wrong, mixed up*)
    end


let cmp_uop (uop : Ast.unop) ((ty, op, st): Ll.ty * Ll.operand * stream) : Ll.ty * Ll.operand * stream=
  let id = gensym "uop" in
  begin match uop with 
  | Lognot -> (ty, Id id,  st>@[I (id, Ll.Binop(Xor, I1, Const 1L, op))])
  | Bitnot -> (ty, Id id, st>@[I (id, Ll.Binop(Xor, I64, Const (-1L), op))])
  | Neg -> (ty, Id id, st>@[I (id, Ll.Binop(Mul, I64, Const (-1L), op))])
  end


let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  begin match exp.elt with
  | CNull x -> (Ptr (cmp_rty x), Null, [])
  | Id x -> let ty, op = Ctxt.lookup x c in
    let id = gensym "id" in
            begin match ty with
            | Ptr (Fun _) -> (ty, op, []) 
            | Ptr ty_inner -> (ty_inner, Id id, [I (id, Load (ty, op))])
    end

  | CInt x -> (I64, Const x, [])
  | CBool x -> if x then (I1, Const 1L, []) else (I1, Const 0L, [])
  | Bop (binop, exp1, exp2) -> (cmp_binop c binop (cmp_exp c exp1) (cmp_exp c exp2))
  | Uop (unop, exp) -> cmp_uop unop (cmp_exp c exp)

  | Index _ ->
    let idx_ptr = gensym "idx" in
    let (ty1, op1, st1) = cmp_lhs c exp in
    (ty1, Id idx_ptr, st1 >@ [I(idx_ptr, Load(Ptr ty1,op1))])

  | CStr s -> let str_gid = gensym "ptr" in 
    let str_uid = gensym "str" in
    let arr = Ll.Array((String.length s) + 1, I8) in
    let stream = [G (str_gid, (arr, GString s))] >@ [I (str_uid, (Gep ((Ptr(arr)), Gid str_gid, [Const 0L; Const 0L])))] in
    (Ptr I8, Ll.Id str_uid, stream)
    
  | CArr (ty, exp_ls) -> 
      let ty_ll = cmp_ty ty in
      let length = Ll.Const (Int64.of_int (List.length exp_ls)) in
      let (ty_alloc, op_alloc, st_alloc) = oat_alloc_array ty length in
      (ty_alloc, op_alloc, st_alloc >@ (execute_exp_list c exp_ls ty_ll ty_alloc op_alloc 0L)) 
      
  
  | NewArr (t, exp) -> 
    let (_, op_array, st_array) = cmp_exp c exp in 
      let (ty_alloc, op_alloc, st_alloc) = oat_alloc_array t op_array in 
        (ty_alloc, op_alloc, st_array >@ st_alloc)

  | Call (call, args) ->
    (*func helper fo ty*)
    let rec cmp_call_helper (arg_s: Ast.exp node list) (args_ty:Ll.ty list): ((Ll.ty * Ll.operand) list * stream)= 
      begin match arg_s, args_ty with
      | x::xs, y::ys ->
        let (args1, arg_code1) = cmp_call_helper xs ys in
          let (args2, arg_code2) = convert_exp c x y in 
            ((y,args2)::args1, arg_code2 >@ arg_code1)
      | [], _ -> ([], [])
      end in 
    let id_ret = gensym "ret" in 
      let (ty_call, op_call, st_call) = cmp_exp c call in
        let (types_func, type_return) = 
          begin match ty_call with 
            | Ptr (Fun (args_ty, return_ty)) -> (args_ty, return_ty) 
            | _ -> failwith "ERORRRAf" 
          end in   
          let (args_for_call, st_args_c) = (cmp_call_helper args types_func) in 
            (type_return, Id id_ret, st_call >@ st_args_c >@ [I (id_ret, Call(type_return, op_call, args_for_call))])

  | _ -> failwith "cmp_exp not implemented"
  end

  and cmp_lhs (c:Ctxt.t) (e:exp node) : (Ll.ty * Ll.operand * stream) =
    begin match e.elt with 
      | Ast.Id idl -> let tylook, op2 = Ctxt.lookup idl c in (tylook, op2, [])
      | Ast.Index (exp1,exp2) -> 
            let (ty1, op1, st1) = cmp_exp c exp1 in
            let (ty2, op2, st2) = cmp_exp c exp2 in
            let ptr = gensym "ptr" in
            let res_typ = begin match ty1 with
              | Ptr(Struct [I64; Array (_, ty)]) -> ty 
              | _ -> failwith "Index: Tried to apply index to non-array"
            end
          in (res_typ, Id ptr, st1 >@ st2 >@ [I (ptr, Gep(ty1, op1, [Ll.Const 0L; Ll.Const 1L; op2]) )])
          
  
  
      | _ -> failwith "cmp_lhs: HEarst geh weg, was soll des? da darft ned sein."
    end

    and execute_exp_list (c:Ctxt.t) (exp_ls: Ast.exp node list) (ty_ll:Ll.ty) (ty_alloc:Ll.ty) (op_alloc:Ll.operand) (idx_counter:int64) : stream = 
      begin match exp_ls with
      | [] -> []
      | exp::exps -> 
        let idx = gensym "idx" in
        let store = gensym "store" in
        let eval_exp_op, eval_exp_st = convert_exp c exp ty_ll in 
        (execute_exp_list c exps ty_ll ty_alloc op_alloc (Int64.add idx_counter 1L)) >@ eval_exp_st >@ [I (store, Store(ty_ll,eval_exp_op, Id idx)); I (idx, Gep(ty_alloc, op_alloc, [Const 0L; Const 1L; Ll.Const idx_counter]))]
      end
    
      
    and convert_exp (c:Ctxt.t) (exp : Ast.exp node) (ty_ll: Ll.ty): (Ll.operand * stream) = 
      let (ty, op, st) = cmp_exp c exp in
      if ty = ty_ll then (op, st)
      else let id = gensym "conv" in
        (Id id, st >@ [I (id, Bitcast (ty, op, ty_ll))])
  
(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

let rec for_helper (vdecl_L:vdecl list): Ast.block = 
begin match vdecl_L with
| x::xs -> (no_loc (Decl x))::for_helper xs
| [] -> []
end 


let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  begin match stmt.elt with
  | Ret (None) -> (c, [T (Ret (Void, None))])
  | Ret (Some(x)) -> let (ty1, op1, st1) = cmp_exp c x in (c, st1 >@ [T (Ret (ty1, Some (op1)))])
  | Decl (id, exp) -> let ty, op, st = cmp_exp c exp in
                      let idg = gensym id in
                      let store = gensym "store" in
                      let c' = Ctxt.add c id (Ptr(ty), Id idg) in
                      (c', st >@ [E (idg, Alloca ty)] >@ [I (store, Store (ty, op, Id idg))]) 

  | Assn (left, right) -> let rty, rop, rst = cmp_exp c right in
                          let lty, lop, lst = cmp_lhs c left in
                          let store = gensym "store" in
                          (c, lst >@ rst >@ [I (store, Store (rty, rop, lop))]) 
  
  | While (cond, body) ->
    let (ty1, op1, st1) = (cmp_exp c cond) in 
      let (body_lbl, done_lbl, cond_lbl) = (gensym "body", gensym "done", gensym "cond") in
        let (c2, st2) = cmp_block c rt body in
          (c2,[(T (Br cond_lbl))] >@ [(L cond_lbl)] >@ st1 >@[(T (Cbr (op1, body_lbl, done_lbl)))] >@ [(L body_lbl)] >@ st2 >@ [T (Br cond_lbl)] >@ [L done_lbl])
          
  | For (vdecl_l, exp1, stmt1, block) -> 
    let (c2, st2) = cmp_block c rt (for_helper vdecl_l) in (*init of the loop*)
      let cnd_f = if (Option.is_some exp1) then Option.get exp1 else no_loc(CBool true) in (*conditon of the loop*)
        let stmt_f = if (Option.is_some stmt1) then [Option.get stmt1] else [] in (*make the statemnet every time*)
          let (c3, st3) = cmp_stmt c2 rt (no_loc (While (cnd_f, stmt_f >@ block))) in  (*make the for loop to a while loop*)
            (c3, st2 >@ st3)
  
  | If (cond, case_if, []) -> 
    let (ty1, op1, st1) = (cmp_exp c cond) in 
      let (then_if, done_lbl) = (gensym "then", gensym "done") in 
        let (c2, x::st2) = cmp_block c rt case_if in
          begin match x with
          | T _ -> (c2, st1 >@ [T (Cbr (op1, then_if, done_lbl))] >@ [(L then_if)] >@ (x::st2) >@ [(L done_lbl)])
          | _ -> (c2, st1 >@ [T (Cbr (op1, then_if, done_lbl))] >@ [(L then_if)] >@ (x::st2) >@ [T (Br done_lbl) ]>@ [(L done_lbl)])
          end
            
  | If (cond, case_if, case_else) -> 
    let (ty1, op1, st1) = (cmp_exp c cond) in 
      let (then_if, else_if, done_lbl) = (gensym "then", gensym "else", gensym "done") in 
        let (c2, x::st2) = cmp_block c rt (case_if) in
          let (c3, y::st3) = cmp_block c2 rt (case_else) in
            begin match x, y with
            | T _, T _->  (c3, st1 >@ [T (Cbr (op1, then_if, else_if))] >@ [(L then_if)] >@ (x::st2) >@ [(L else_if)] >@ (y::st3))
            | T _ , _ -> (c3, st1 >@ [T (Cbr (op1, then_if, else_if))] >@ [(L then_if)] >@ (x::st2) >@ [(L else_if)] >@ (y::st3) >@ [T (Br done_lbl)] >@ [(L done_lbl)])
            | _, T _ -> (c3, st1 >@ [T (Cbr (op1, then_if, else_if))] >@ [(L then_if)] >@ (x::st2) >@ [T (Br done_lbl)] >@ [(L else_if)] >@ (y::st3) >@ [(L done_lbl)])
            | _ , _ -> (c3, st1 >@ [T (Cbr (op1, then_if, else_if))] >@ [(L then_if)] >@ (x::st2) >@ [T (Br done_lbl)] >@ [(L else_if)] >@ (y::st3) >@ [T (Br done_lbl)] >@ [(L done_lbl)])
            end      
            
  | SCall (func_id, args) -> let (ty, op, st) = cmp_exp c (no_loc (Call (func_id, args))) in  (*Might be wrong*)
  (c, st)
            
  end

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts


  


(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)

let rec helper_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  begin match p with
    | [] -> c
    | pro::pros -> begin match pro with
                    | Ast.Gvdecl {elt; loc} -> let t = begin match elt.init.elt with
                                                  | Ast.CNull t -> cmp_ty (TRef (t))
                                                  | Ast.CBool t ->  cmp_ty TBool
                                                  | Ast.CInt t ->  (cmp_ty TInt)
                                                  | Ast.CArr (t, ex) -> Ptr (Struct [I64; Array(List.length ex, cmp_ty t)])
                                                  | Ast.CStr s -> Ptr (Array(1 + String.length s, I8)) (*unsure if correct*)
                                                  | _ -> failwith "Global variable case not implemented"
                                                  end 
                                                in helper_global_ctxt (Ctxt.add c elt.name (Ptr t, Gid elt.name)) pros
                    | Ast.Gfdecl {elt; loc} -> helper_global_ctxt c pros
                    end
    end

let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  helper_global_ctxt c p
  

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

 let rec create_space_fdecl (c:Ctxt.t) (arg_typ: Ll.ty list) (arg_id: Ll.uid list): Ctxt.t * (elt list) = (*Allocs the space*)
 begin match arg_typ, arg_id with
 | ty::tys, id::ids -> 
  let id_ptr = gensym "ptr" in 
    let id_store = gensym "store" in 
      let c1, st = create_space_fdecl c tys ids in 
        (Ctxt.add c1 id (Ptr (ty), Id id_ptr), [(I (id_store, Store (ty, Id id, Id id_ptr))); (E (id_ptr, Alloca ty))] >@ st)
  | [], [] -> (c, [])
  | _, _ -> failwith "create space has wrong input"
 end


 (*get all the functiom declations*)
let rec get_arg_fdecl (args: (ty * id) list): uid list = 
 begin match args with
 | (_, id)::xs -> (id::(get_arg_fdecl xs))
 | [] -> []
 | _ -> failwith "args something wrong cmp_fdecl"
 end

let rec get_typ_fdecl (args: (ty * id) list): Ll.ty list = 
 begin match args with
 | (ty, _)::xs -> (cmp_ty ty)::(get_typ_fdecl xs)
 | [] -> []
 | _ -> failwith "type is something cmp_fdecl"
 end

let get_arg_typ_fdecl (args: (ty * id) list) (ret_ty: ret_ty): (uid list * (Ll.ty list * Ll.ty)) = 
 (get_arg_fdecl args, (get_typ_fdecl args, cmp_ret_ty ret_ty))

let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list = 
  let {frtyp; fname; args; body} = f.elt in (*ret type, id, arguments, block*)
  let (args_id, (args_ty, ret_ty)) = get_arg_typ_fdecl args frtyp in
    let c2, st_alloc = create_space_fdecl c args_ty args_id in 
      let c3, st_block = cmp_block c2 ret_ty body in 
        let cfg_comp, id_gdecl = cfg_of_stream (st_alloc >@ st_block) in 
          ({f_ty = (args_ty, ret_ty); f_param = args_id; f_cfg = cfg_comp}, id_gdecl)



(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  begin match e.elt with
    | Ast.CNull t -> ((Ptr (cmp_rty t), GNull),[])
    | Ast.CBool b -> ((I1, GInt (if b then 1L else 0L)),[])
    | Ast.CInt i -> ((I64, GInt i),[])
    | Ast.CStr s -> let gid = gensym "str" in
    let ret_ty = Array(String.length s + 1, I8) in
    (Ptr ret_ty, GGid gid), [gid, (ret_ty, GString s)]

    | Ast.CArr (ty, exps) -> 
      let rec get_ty_ginit (exps_f: Ast.exp node list) : Ll.gdecl list * (Ll.gid * Ll.gdecl) list = (*compile exp to gdecl and gid gdecl*)
        begin match exps_f with
        | x::xs -> 
          let (g_dec, gid_gdec_list) = cmp_gexp c x in
            let (g_dec_list, gid_gdec_list2) = get_ty_ginit xs in 
              (g_dec::g_dec_list, gid_gdec_list @ gid_gdec_list2)
        | [] -> ([], [])
        end in 
        let id_array = gensym "garray" in
          let ty_ll = cmp_ty ty in
            let array_length = List.length exps in 
              let decls, gid_decls = get_ty_ginit exps in 
              let array_ty = Struct [I64; Array(array_length, ty_ll)] in 
                let array_ginit = GStruct [I64, GInt (Int64.of_int array_length); Array( array_length, ty_ll), GArray decls] in 
                  (Ptr array_ty, GGid id_array), [(id_array, (array_ty, array_ginit))]@gid_decls

    | _ -> failwith "cmp_gexp: illegal case"
  end

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }