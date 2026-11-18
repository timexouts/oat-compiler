(* ll ir compilation -------------------------------------------------------- *)

open Ll
open Llutil
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be represented
   in 64 bit. This greatly simplifies code generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  fun ll_op ->  
    (* Printf.printf("LL op: %s\n") (Llutil.string_of_operand ll_op); *)
    begin match ll_op with  
    | Const x -> (Movq, [Imm (Lit x); dest])
    | Gid x -> (Leaq, [Ind3 (Lbl (Platform.mangle x), Rip); dest])
    | Id x -> (*Printf.printf("Lookup %s\n") (x);*)(Movq, [(lookup ctxt.layout x); dest])
    | Null -> (Movq, [Imm (Lit 0L); dest])
    end



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)

let n_to_reg (i:int) = 
  begin match i with
  | 0 -> Reg Rdi
  | 1 -> Reg Rsi
  | 2 -> Reg Rdx
  | 3 -> Reg Rcx
  | 4 -> Reg R08
  | 5 -> Reg R09
  | _ -> failwith "No not here"
  end

let rec call_par (ctxt:ctxt)  (param: (ty * Ll.operand) list) (n_para: int)=
  begin match param with
  | (ty, op)::xs when n_para < 5 -> [compile_operand ctxt (n_to_reg n_para) op] @ (call_par ctxt xs (n_para + 1))
  | (ty, op)::xs when n_para = 5 -> [compile_operand ctxt (n_to_reg n_para) op] @ (List.rev (call_par ctxt xs (n_para + 1)))
  | (ty, op)::xs -> [(Pushq, [Reg R12]);(compile_operand ctxt (Reg R12) op)] @ (call_par ctxt xs (n_para + 1))
  | [] -> []
  end 

let compile_call (ctxt:ctxt) (uid:uid) (ret_ty: Ll.ty) (func_call: gid) (param: (ty * Ll.operand) list) =
  (*if(List.length param % 2 != 0) then [(Pushq, [Imm(Lit 0L)])] @ (*to make the stack 16 byte aligned*)*)
  let stack_p = Int64.of_int (((List.length param) - 6)) in 
    [(Subq, [Imm (Lit 0x8L); Reg Rsp]); (Andq, [Imm (Lit 0xFFFFFFFFFFFFFFF0L); Reg Rsp])] @ (* Align 16 byte*)
    (if (stack_p > 0L && Int64.rem stack_p 2L != 0L) then 
      [(Pushq, [Imm (Lit 0L)])] 
    else
      [])
      (* (Platform.mangle gid) *)
    @ (call_par ctxt param 0) @ [(Callq, [Imm (Lbl func_call)])] @ 
    begin match ret_ty with
    | Void -> []
    | _ -> [(Movq, [Reg Rax; lookup ctxt.layout uid])]
    end


(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec resolve_lbl_ty ((name, e_type)::xs:(tid * ty) list) (t:tid) = if (String.equal name t) then e_type else resolve_lbl_ty xs t(*if xs != [] then resolve_lbl_ty xs t*)

let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  begin match t with
  | Namedt x -> size_ty tdecls (resolve_lbl_ty tdecls x)
  | Array (size, Namedt x) -> size_ty tdecls (Array (size, (resolve_lbl_ty tdecls x)))
  | Struct ((Namedt x)::[]) -> size_ty (tdecls) (Struct ((resolve_lbl_ty tdecls x)::[])) 
  | Struct ((Namedt x)::xs) -> size_ty (tdecls) (Struct ((resolve_lbl_ty tdecls x)::xs)) 
  | Void -> 0
  | I1 -> 8
  | I8 -> 0
  | I64 -> 8
  | Ptr x -> 8
  | Fun (x1, x2) -> 0
  | Array (size, e_type) -> size * (size_ty tdecls e_type)
  | Struct (x::[]) -> (size_ty tdecls x)
  | Struct (x::xs) -> (size_ty tdecls x) + size_ty tdecls (Struct xs) 
  | _ -> failwith "size_ty not implemented"
  end
  



(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)

let rec resolve_struct (ctxt : ctxt) (cur_pos : int64) (cur_type : Ll.ty list) : int64 =
  begin match cur_pos, cur_type with
  | 0L, _ -> 0L
  | _, t::ts -> Int64.add (Int64.of_int (size_ty ctxt.tdecls t)) (resolve_struct ctxt (Int64.sub cur_pos 1L) ts)
  | _, _ -> failwith "something aint right"
end


let rec resolve_pointer (ctxt:ctxt) (cur_typ : Ll.ty) (path: Ll.operand list) : X86.ins list =
  (* Printf.printf("Resolve pointer\n"); *)
  begin match cur_typ, path with
    | _, [] -> []
    | Void, _ -> []
    | I1, _ -> []
    | I8, _ -> []
    | I64, _ -> []
    | Ptr x, _ -> []
    | Struct tys, (Const p)::ps -> (Addq, [Imm (Lit (resolve_struct ctxt p tys)); Reg R08])::(resolve_pointer ctxt (List.nth tys (Int64.to_int p)) ps)
    | Array (size, ty), p::ps -> [(compile_operand ctxt (Reg R09) p); (Imulq, [Imm (Lit(Int64.of_int(size_ty ctxt.tdecls ty))); Reg R09]);(Addq, [Reg R09;Reg R08])] @ (resolve_pointer ctxt ty ps)
    | Fun _, _ -> []
    | Namedt x, (Const p)::ps -> resolve_pointer ctxt (resolve_lbl_ty ctxt.tdecls x) (Const p::ps)
    | _, _-> failwith "Issue resolving pointer"
  end

let rec pr_gep (path: Ll.operand list) =
  begin match path with
  | [] -> Printf.printf("End\n")
  | (Const x)::xs -> Printf.printf("Const: %s\n") (Int64.to_string x); pr_gep xs
  | (Gid x)::xs -> Printf.printf("Gid: %s\n") (x); pr_gep xs
  | (Id x)::xs -> Printf.printf("Id: %s\n") (x); pr_gep xs
  | _ -> failwith "Not implemented"
  end

let compile_gep (ctxt:ctxt) (op: Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  (* Printf.printf("Compiling Gep\n");
  Printf.printf("Type: %s\n") (string_of_ty (fst op));
  Printf.printf("Operand: %s\n") (Llutil.string_of_operand (snd op)); *)
  (* Printf.printf("Location of ty") *)
  (* pr_gep path; *)
  let p::ps = path in
  begin match (fst op) with
    | Ptr x -> compile_operand ctxt (Reg R08) (snd op)::[(compile_operand ctxt (Reg R09) p); (Imulq, [Imm (Lit(Int64.of_int(size_ty ctxt.tdecls (fst op)))); Reg R09]);(Addq, [Reg R09;Reg R08])] @ (resolve_pointer ctxt x ps)
    | _ -> failwith "Not a pointer"
  end



(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let create_bop_ins (bin_oper:bop) (o_type:ty) (op1: Ll.operand) (op2: Ll.operand) (u:uid) (ctxt:ctxt)= 
  [(compile_operand ctxt (Reg R09) op1); compile_operand ctxt (Reg Rcx) op2] @
  begin match bin_oper with
  | Add -> [(Addq, [Reg Rcx; Reg R09])]  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | Sub -> [(Subq, [Reg Rcx; Reg R09])] (*changed operands*)  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | Mul -> [(Imulq, [Reg Rcx; Reg R09])]  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | Shl -> [(Shlq, [Reg Rcx;Reg R09])] (*fail rcx *)  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | Lshr -> [(Shrq, [Reg Rcx; Reg R09])] (*fail*)  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | Ashr -> [(Sarq, [Reg Rcx; Reg R09])] (*fail*)  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | And -> [(Andq, [Reg Rcx; Reg R09])]  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | Or -> [(Orq, [Reg Rcx; Reg R09])]  @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  | Xor -> [(Xorq, [Reg Rcx; Reg R09])] @ [(Movq, [Reg R09; (lookup ctxt.layout u)])]
  end

let icmp_ins (ctxt:ctxt) (uid:uid) (op1: Ll.operand) (op2: Ll.operand) (cnd:Ll.cnd) = 
  [(compile_operand ctxt (Reg R08) op1); compile_operand ctxt (Reg R09) op2; (Cmpq, [Reg R09; Reg R08])]@ (* Check both side R09 <-> R08*)
  [(Movq, [Imm (Lit 0L); Reg R08]); (Set (compile_cnd cnd), [Reg R08]); (Movq, [Reg R08; lookup ctxt.layout uid])]
  

let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  (* Printf.printf("Compiling insn\n"); *)
  begin match i with
  | Binop (bin_oper, o_type, op1, op2) -> create_bop_ins bin_oper o_type op1 op2 uid ctxt
  | Alloca ty -> [(Subq, [Imm (Lit 8L); Reg Rsp]); (Movq, [Reg Rsp; lookup ctxt.layout uid])]
  | Load (ty, op) -> [compile_operand ctxt (Reg R08) op; (Movq, [Ind2 R08; Reg R08]); (Movq, [Reg R08; lookup ctxt.layout uid])]
  | Store (ty, op1, op2) -> [(compile_operand ctxt (Reg R08) op1); (compile_operand ctxt (Reg R09) op2); (Movq, [Reg R08; Ind2 R09])]
  | Icmp (cnd, ty, op1, op2) -> icmp_ins ctxt uid op1 op2 cnd
  | Call (ty1, Gid func_call, para) -> compile_call ctxt uid ty1 func_call para
  | Bitcast (ty1, op, ty2) -> [compile_operand ctxt (Reg R08) op; (Movq, [Reg R08; lookup ctxt.layout uid])] (*[(compile_operand ctxt (Reg R08) op); (Movq, [Reg R08; lookup ctxt.layout uid])]*)
  | Gep (ty, op1, op2) -> compile_gep ctxt (ty, op1) (op2) @ [(Movq, [Reg R08; lookup ctxt.layout uid])]
  | _ -> failwith "compile_insn not implemented"
  end

(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)



let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  (* Printf.printf("I will terminate you hehe: %s\n") fn; *)
  begin match t with
    | Ret (_, None) -> [(Movq, [Reg Rbp; Reg Rsp]);(Popq, [Reg Rbp]); (Retq, [])] (*could change to retq*) 
    | Ret (ts, Some op) -> [(compile_operand ctxt (Reg Rax) op);(Movq, [Reg Rbp; Reg Rsp]);(Popq, [Reg Rbp]); (Retq, [])]
    | Br (lbl) -> [(Jmp, [Imm (Lbl (mk_lbl fn lbl))])] (*maybe put lbl in the mk_lbl function*)
    | Cbr (op, lbl1, lbl2) -> 
      [
      (* (Pushq, [Reg R08]); save contents of R08 on stack; debug: might lead to issue to due having fixed layout *)
      compile_operand ctxt (Reg R08) op; 
      (Cmpq, [Imm (Lit 1L); Reg R08]); (*Is it really an Imm? *)
      (* (Popq, [Reg R08]); pop contents back in R08 *)
      (J Eq, [Imm (Lbl (mk_lbl fn lbl1))]); (*maybe put lbl in the mk_lbl function*)
      (Jmp, [Imm (Lbl (mk_lbl fn lbl2))]) (*maybe put lbl in the mk_lbl function*)
        ]
        
    (* | _ -> failwith "compile_terminator case not included" *)
  end

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  let (local_id, term) = blk.term in
  (List.flatten (List.concat_map (fun x -> [compile_insn ctxt x]) blk.insns)) @ (compile_terminator fn ctxt term)


let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


let create_asm (n:int) : operand = failwith "unimplemented"

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  begin match n with
    | 0 -> Reg Rdi
    | 1 -> Reg Rsi
    | 2 -> Reg Rdx
    | 3 -> Reg Rcx
    | 4 -> Reg R08
    | 5 -> Reg R09
    | i -> Ind3 (Lit (Int64.mul(Int64.of_int(Int.sub i 4)) 8L), Rbp) (*Calculates the offset from the BP*)
  end
(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)

let calc_stack_addresse (offset:int64) (cur_para:int64) = Ind3 (Lit (Int64.add offset (Int64.mul cur_para (-8L))), Rbp)

let rec layout_args (cur_para:int64) (args : uid list): layout = (*get data when more than 6*)
  begin match args with
  | x::xs -> (x, calc_stack_addresse 0L cur_para)::(layout_args (Int64.add cur_para 1L) xs) (*Ind3(Lit (Int64.mul cur_para (-8L)), Rbp)*)
  | x::[] -> (x, calc_stack_addresse 0L cur_para)::[]
  | [] -> []
  end

(*Without calls, *)
let rec layout_res (cur_para:int64) (offset: int64) (uid_ins_list: (uid * insn) list): layout = (*Printf.printf ("inst: %s \n") (string_of_insn instruction);*)
  begin match uid_ins_list with
    | [] -> []
    | (identifier, Binop _)::rest -> (identifier, calc_stack_addresse offset cur_para)::(layout_res (Int64.add 1L cur_para) offset rest)
    | (identifier, Alloca _)::rest -> (identifier, calc_stack_addresse offset cur_para)::(layout_res (Int64.add 1L cur_para) offset rest) (*get one more offset*)
    | (identifier, Load _)::rest -> (identifier, calc_stack_addresse offset cur_para)::(layout_res (Int64.add 1L cur_para) offset rest)
    | (identifier, Store _)::rest -> layout_res cur_para offset rest
    | (identifier, Icmp _)::rest -> (identifier, calc_stack_addresse offset cur_para)::(layout_res (Int64.add 1L cur_para) offset rest)
    | (identifier, Call _)::rest -> (identifier, calc_stack_addresse offset cur_para)::(layout_res (Int64.add 1L cur_para) offset rest)
    | (identifier, Bitcast _)::rest -> (identifier, calc_stack_addresse offset cur_para)::(layout_res (Int64.add 1L cur_para) offset rest)
    | (identifier, Gep _)::rest -> (identifier, calc_stack_addresse offset cur_para)::(layout_res (Int64.add 1L cur_para) offset rest)
    | _ -> failwith "no type of inst"
  end

let rec print_bs ((lbl, x)::xs: (lbl * block) list) = 
  Printf.printf ("%s: %s \n") (lbl) (string_of_block x); if xs != [] then print_bs xs



let rec block_layout_resolver (lbl_block : (lbl * block) list) : (uid * insn) list =
  begin match lbl_block with
    | [] -> []
    | (lbl, block)::lbl_blocks -> block.insns @ (block_layout_resolver lbl_blocks)
  end

(*Maybe need to implement red zone*)
let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout = 
  (*if block.insns != [] then (Printf.printf ("First:\n%s \n") (string_of_block block)); if lbled_blocks != [] then (print_bs lbled_blocks); Printf.printf ("---------------------------------------------\n");*)
  let offset = (Int64.neg (Int64.mul (Int64.add (Int64.of_int (List.length args)) 0L) 8L)) in 
    let blocks = block_layout_resolver (("", block)::lbled_blocks) in
      (layout_args 1L args) @ if blocks != [] then (layout_res 1L offset blocks) else []

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)

let rec block_assembler (name:string) (ctxt:ctxt) ( lab_blocks : (lbl * block) list): X86.elem list =
  (* Printf.printf("Block assembler\n"); *)
  begin match lab_blocks with       
    | [] -> []
    | (lbl, block)::ls -> (*Printf.printf("Labeled block:\n %s \n") (string_of_asm(compile_lbl_block name lbl ctxt block).asm) ;*)(compile_lbl_block name lbl ctxt block)::(block_assembler name ctxt ls)
  end 

let rec set_args (f_param : uid list) (arg_num : int) (layout: layout): ins list = 
  begin match f_param, arg_num with
    | [], _ -> [] 
    | arg::args, 0|arg::args,1|arg::args,2|arg::args,3|arg::args,4|arg::args,5 ->  (Movq, [arg_loc arg_num; lookup layout arg])::(set_args args (arg_num + 1) layout)
    | arg::args, arg_num -> (Movq, [arg_loc arg_num; Reg R12])::(Movq, [Reg R12; lookup layout arg])::(set_args args (arg_num + 1) layout)
  end 
  
let rec layout_printer (layout:layout) : unit =
  begin match layout with
  | [] -> ()
  | (uid, operand)::xs -> Printf.printf("UID: %s, Operand: %s\n") (uid) (X86.string_of_operand operand); layout_printer xs
  end

let rec tdecl_printer (tdecls:(tid * ty) list) : unit =
  begin match tdecls with
  | [] -> ()
  | t::ts -> Printf.printf("Type: %s\n") (string_of_named_tdecl t); tdecl_printer ts
  end

let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
  let ctxt = { tdecls; layout =  (stack_layout f_param f_cfg) } in
    let fst_block = fst f_cfg in
      let lab_blocks = snd f_cfg in
        let init_offset = Int64.of_int(Int.mul (List.length ctxt.layout) (-8)) in
          let setup = [(Pushq, [Reg Rbp]); (Movq, [Reg Rsp; Reg Rbp]); (Addq, [Imm(Lit init_offset); Reg Rsp])] in
            let args = set_args f_param 0 ctxt.layout in
              begin match lab_blocks with
                | [] ->[{lbl = name; global = true; asm = Text (setup @ args @ compile_block name ctxt fst_block)}]
                | _ -> {lbl = name; global = true; asm = Text (setup @ args @ compile_block name ctxt fst_block)}::(block_assembler name ctxt lab_blocks)
              end

(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)