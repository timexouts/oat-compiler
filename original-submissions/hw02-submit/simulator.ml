
(* Run "eval $(opam env)" *)
(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x -> 
  begin match x with
    | Eq -> fz
    | Neq -> (false = fz)
    | Lt -> ((fs = true) && (fo = false)) || ((fs = false) && (fo = true))
    | Le -> ((fs = true) && (fo = false)) || ((fs = false) && (fo = true)) || (true = fz)
    | Gt -> not (((fs = true) && (fo = false)) || ((fs = false) && (fo = true)) || (true = fz))
    | Ge -> not (((fs = true) && (fo = false)) || ((fs = false) && (fo = true)))
  end

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option = begin
  if (addr < mem_bot) then ((*(Printf.printf("Address problem: %Ld\n") addr);*) None) (* Change raise... to None*)
  else if (addr >= mem_top) then None (* Change raise... to None*)
  else (Some (Int64.to_int (Int64.sub addr 0x400000L)))
end



  let load_m (o:operand) (m:mach): quad = 
    begin match o with
      | Imm Lit x -> x
      | Reg x -> m.regs.(rind x)
      | Ind1 Lit x -> int64_of_sbytes (Array.to_list (Array.sub m.mem (Option.get (map_addr x)) 8))
      | Ind2 x -> int64_of_sbytes (Array.to_list (Array.sub m.mem (Option.get (map_addr m.regs.(rind x))) 8))
      | Ind3 (Lit y, x) -> int64_of_sbytes (Array.to_list (Array.sub m.mem (Option.get (map_addr (Int64.add m.regs.(rind x) y))) 8))
      | _ -> raise (Invalid_argument "Label not allowed")  (*Only Labels fall into her but that should not be possible*)
    end
  
  let store_m (o:operand) (m:mach) (q:quad): unit = 
    begin match o with
      | Imm Lit x -> raise (Invalid_argument "Can not save to an imm") (* Not Possible*)
      | Reg x -> Array.set m.regs (rind x) q
      | Ind1 Lit x -> Array.blit (Array.of_list (sbytes_of_int64 q)) 0 m.mem (Option.get (map_addr x)) 8 (*Copies the elements Array to the memory*)
      | Ind2 x -> Array.blit (Array.of_list (sbytes_of_int64 q)) 0 m.mem (Option.get (map_addr m.regs.(rind x))) 8 (*Source_array start_of_src memory start_of_mem length*)
      | Ind3 (Lit y, x) -> Array.blit (Array.of_list (sbytes_of_int64 q)) 0 m.mem (Option.get (map_addr (Int64.add m.regs.(rind x) y))) 8
      | _ -> raise (Invalid_argument "Not known argument")
    end

    (* let store_m_cc (o:operand) (m:mach) (q:quad): unit = 
      begin match o with
        | Imm Lit x -> raise (Invalid_argument "Can not save to an imm") (* Not Possible*)
        | Reg x ->  Array.set m.regs (rind x) q
        | Ind1 Lit x -> Array.blit (Array.of_list (sbytes_of_int64 q)) 0 m.mem (Int.add (Option.get (map_addr x)) 0) 1 (*Copies the elements Array to the memory*)
        | Ind2 x -> Printf.printf("Sbytes %s") (sbytes_of_int64 q);Array.blit (Array.of_list (sbytes_of_int64 q)) 0 m.mem (Int.add (Option.get (map_addr m.regs.(rind x))) 0) 1 (*Source_array start_of_src memory start_of_mem length*)
        | Ind3 (Lit y, x) -> Array.blit (Array.of_list (sbytes_of_int64 q)) 0 m.mem (Int.add (Option.get (map_addr (Int64.add m.regs.(rind x) y))) 0) 1
        | _ -> raise (Invalid_argument "Not known argument")
      end *)

  let calc_address (o:operand) (m:mach) : quad =
    begin match o with
      | Ind1 Lit x -> x
      | Ind2 reg -> m.regs.(rind reg)
      | Ind3 (Lit imm, reg) -> Int64.add m.regs.(rind reg) imm
      | _ -> raise(Invalid_argument "Anything but Ind operands not allowed")
    end
  
  let set_flags (q:quad) (m:mach): unit = if Int64.equal q 0L then m.flags.fz <- true else m.flags.fz <- false; 
                                          if Int64.equal (Int64.max q (-1L)) (-1L) then m.flags.fs <- true else m.flags.fs <- false

  (* must be applied before the shift and only if AMT = 1*)
  let set_fo_shlq (q:quad) (m:mach) : unit = if ((Int64.equal 0L (Int64.shift_right_logical q 62)) || (Int64.equal 3L (Int64.shift_right_logical q 62)))
    then m.flags.fo <- false else m.flags.fo <- true (*is ocaml little or big endian*)

  (* must be applied on the result of the shift*)
  let set_fs_fz_shrq (q:quad) (m:mach) : unit = if (Int64.equal 0L (Int64.shift_right_logical q 63)) then m.flags.fs <- false else m.flags.fs <- true;
                                                if (Int64.equal 0L q) then m.flags.fz <- true else m.flags.fz <- false

  (* must be applied before the shift and only if AMT = 1 *)
  let set_fo_shrq (q:quad) (m:mach) : unit = if (Int64.equal 1L (Int64.shift_right_logical q 63)) then m.flags.fo <- true else m.flags.fo <- false

  open Int64_overflow
  
  let step (m:mach) : unit = 
    begin match m.mem.(Option.get (map_addr m.regs.(rind Rip))) with
      | InsFrag -> ()
      | InsB0 x -> 
        begin match x with
          (*Data-movement Instructions*)
          | Movq, a::b::[] -> store_m b m (load_m a m)(*first loads quad then saves it*); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Pushq, a::[] -> m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L; store_m (Ind2 Rsp) m (load_m a m); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
            (* Array.set m.regs (rind Rsp) (Int64.sub m.regs.(rind Rsp) 8L); store_m (Ind2 Rsp) m (load_m a m); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L *)
          (*m.regs(rind Rsp) <- (Int64.sub m.regs.(rind Rsp) 8L) Is the same*)
          | Popq, a::[] -> store_m a m (load_m (Ind2 Rsp) m); Array.set m.regs (rind Rsp) (Int64.add m.regs.(rind Rsp) 8L); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Leaq, a::b::[] -> store_m b m (calc_address a m); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          (*Logic Instructions*)
          | Notq, a::[] -> store_m a m (Int64.lognot (load_m a m)); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Andq, a::b::[] -> store_m b m (Int64.logand (load_m a m) (load_m b m)); set_flags (load_m b m) m; m.flags.fo <- false; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Orq, a::b::[] -> store_m b m (Int64.logor (load_m a m) (load_m b m)); set_flags (load_m b m) m; m.flags.fo <- false; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Xorq, a::b::[] -> store_m b m (Int64.logxor (load_m a m) (load_m b m)); set_flags (load_m b m) m; m.flags.fo <- false; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          (*Bit-manipulation Instructions*)
          | Sarq, (Imm Lit a)::b::[] -> 
            begin match a with (*check which shift amount is entered and set result/flags accordingly*)
              | 0L -> ()
              | 1L -> store_m b m (Int64.shift_right (load_m b m) 1); set_flags (load_m b m) m; m.flags.fo <- false
              | amount -> store_m b m (Int64.shift_right (load_m b m) (Int64.to_int amount)); set_flags (load_m b m) m;
            end; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Sarq, (Reg Rcx)::b::[] ->
            begin match m.regs.(rind Rcx) with
              | 0L -> ()
              | 1L -> store_m b m (Int64.shift_right (load_m b m) 1); set_flags (load_m b m) m; m.flags.fo <- true
              | amount -> store_m b m (Int64.shift_right (load_m b m) (Int64.to_int amount)); set_flags (load_m b m) m;
            end; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Shlq, (Imm Lit a)::b::[] ->
            begin match a with (*check which shift amount is entered and set result/flags accordingly*)
              | 0L -> ()
              | 1L -> set_fo_shlq (load_m b m) m; store_m b m (Int64.shift_left (load_m b m) 1); set_flags (load_m b m) m; 
              | amount -> store_m b m (Int64.shift_left (load_m b m) (Int64.to_int amount)); set_flags (load_m b m) m;
            end; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Shlq, (Reg Rcx)::b::[] ->
            begin match m.regs.(rind Rcx) with (*check which shift amount is entered and set result/flags accordingly*)
              | 0L -> ()
              | 1L -> set_fo_shlq (load_m b m) m; store_m b m (Int64.shift_left (load_m b m) 1); set_flags (load_m b m) m; 
              | amount -> store_m b m (Int64.shift_left (load_m b m) (Int64.to_int amount)); set_flags (load_m b m) m;
            end; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Shrq, (Imm Lit a)::b::[] ->
            begin match a with (*check which shift amount is entered and set result/flags accordingly*)
              | 0L -> ()
              | 1L -> set_fo_shrq (load_m b m) m; store_m b m (Int64.shift_right_logical (load_m b m) 1); set_fs_fz_shrq (load_m b m) m; 
              | amount -> store_m b m (Int64.shift_right_logical (load_m b m) (Int64.to_int amount)); set_fs_fz_shrq (load_m b m) m;
            end; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Shrq, (Reg Rcx)::b::[] ->
            begin match m.regs.(rind Rcx) with (*check which shift amount is entered and set result/flags accordingly*)
              | 0L -> ()
              | 1L -> set_fo_shrq (load_m b m) m; store_m b m (Int64.shift_right_logical (load_m b m) 1); set_fs_fz_shrq (load_m b m) m; 
              | amount -> store_m b m (Int64.shift_right_logical (load_m b m) (Int64.to_int amount)); set_fs_fz_shrq (load_m b m) m;
            end; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Set a , b::[] -> if (interp_cnd m.flags a) then store_m b m (Int64.add (Int64.logand (load_m b m) 0xFFFFFFFFFFFFFF00L) 1L) else store_m b m (Int64.logand (load_m b m) 0xFFFFFFFFFFFFFF00L); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          (*Arithmetic Instructions*)
          | Negq, a::[] -> m.flags.fo <- (neg (load_m a m)).overflow; store_m a m ((neg (load_m a m)).value); set_flags (load_m a m) m; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Addq, a::b::[] -> m.flags.fo <- (add (load_m a m) (load_m b m)).overflow;
                              store_m b m ((add (load_m a m) (load_m b m)).value);
                              set_flags (load_m b m) m; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Subq, a::b::[] -> m.flags.fo <- (sub (load_m b m) (load_m a m)).overflow; (*Printf.printf("Bool: %b") ((sub (load_m b m) (load_m a m)).overflow);*)
                              if (load_m a m = Int64.min_int) then m.flags.fo <- true;
                              store_m b m ((sub (load_m b m) (load_m a m)).value);
                              set_flags (load_m b m) m; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L;
          | Imulq, a::b::[] -> m.flags.fo <- (mul (load_m a m) (load_m b m)).overflow;
                              store_m b m ((mul (load_m a m) (load_m b m)).value);
                              set_flags (load_m b m) m; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Incq, a::[] -> m.flags.fo <- (succ (load_m a m)).overflow;
                            store_m a m ((succ (load_m a m)).value);
                            set_flags (load_m a m) m; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Decq, a::[] ->  m.flags.fo <- (pred (load_m a m)).overflow;
                            store_m a m ((pred (load_m a m)).value);
                            set_flags (load_m a m) m; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          (*Control-flow and condition Instructions*)
          | Cmpq, a::b::[] -> set_flags ((sub (load_m b m) (load_m a m)).value) m; m.flags.fo <- (sub (load_m b m) (load_m a m)).overflow; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          | Jmp, a::[] -> store_m (Reg Rip) m (load_m a m)
          | Callq, a::[] -> m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L; m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L; store_m (Ind2 Rsp) m (load_m (Reg Rip) m); m.regs.(rind Rip) <- load_m a m
            (* Array.set m.regs (rind Rsp) (Int64.sub m.regs.(rind Rsp) 8L); store_m (Ind2 Rsp) m (load_m (Reg Rip) m); store_m (Ind2 Rip) m (load_m a m) *)
          | Retq, [] -> store_m (Reg Rip) m (load_m (Ind2 Rsp) m); Array.set m.regs (rind Rsp) (Int64.add m.regs.(rind Rsp) 8L); 
            (* store_m (Reg Rip) m (load_m (Ind2 Rsp) m); Array.set m.regs (rind Rsp) (Int64.add m.regs.(rind Rsp) 8L); m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L *)
          | J a, b::[] -> if (interp_cnd m.flags a) then store_m (Reg Rip) m (load_m b m) else m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
          (*Errors V *)
          | _ -> raise (Invalid_argument "Not know command")
        end
      | _ -> ()
    end
 


(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)

type label_pos = {
  lbl : lbl;
  lbl_pos : quad;
  next_seg_after_last_txt : quad 
}

(* type text_list = elem list
type data_list = elem list *)

(* let text_list : elem list = []
let data_list : elem list = [] *)


let rec create_text_seg (p:prog) : elem list =
  begin match p with
    | [] -> []
    | el::els -> begin match el.asm with
                  | Text a -> el::(create_text_seg els )
                  | Data a -> (create_text_seg els)
                end
  end

let rec create_data_seg (p:prog): elem list =
  begin match p with
    | [] -> []
    | el::els -> begin match el.asm with
                  | Text a -> (create_data_seg els)
                  | Data a -> el::(create_data_seg els)
                end
  end


let rec data_to_sbyte (data : data list) : sbyte list =
  begin match data with 
    | [] -> []
    | d::ds -> (sbytes_of_data d) @ (data_to_sbyte ds)
  end

let rec ins_to_sbyte (ins : ins list) : sbyte list = 
  begin match ins with
    | [] -> []
    | i::is -> (sbytes_of_ins i) @ (ins_to_sbyte is)
  end


let length_asm (asm : asm) : int64 =
  begin match asm with
    | Text a -> Int64.mul (Int64.of_int (List.length a)) 8L
    | Data a -> Int64.of_int (List.length (data_to_sbyte a)) 
  end

let rec extract_data (elem : elem list) : sbyte list =
    begin match elem with
      | [] -> []
      | e::es -> begin match e.asm with
        | Text a -> raise (Invalid_argument "This function must not be called with Text asm")
        | Data a -> (data_to_sbyte a)@(extract_data es)
      end
    end

let rec find_label (labels : label_pos list) (name : string): int64 = (* returns offset of specific label*)
  begin match labels with 
    | [] -> raise (Undefined_sym name)
    | l::ls -> if (l.lbl = name) then (Int64.add l.lbl_pos 0x400000L) else find_label ls name
  end


let rec label_to_address (ins : ins list) (labels: label_pos list) : ins list =
  begin match ins with
    | [] -> []
    | i::is -> begin match i with (* check if instruction contains a label, if yes replace it with mem address*)
                | (op, [Imm (Lbl a); Imm (Lbl b)]) -> (op, [Imm (Lit (find_label labels a)); Imm (Lit (find_label labels b))])::(label_to_address is labels)
                | (op, [Imm (Lbl a); Ind1 (Lbl b)]) -> (op, [Imm (Lit (find_label labels a)); Ind1 (Lit (find_label labels b))])::(label_to_address is labels)
                | (op, [Ind1 (Lbl a); Ind1 (Lbl b)]) -> (op, [Ind1 (Lit (find_label labels a)); Ind1 (Lit (find_label labels b))])::(label_to_address is labels)
                | (op, [Ind1 (Lbl a); Imm (Lbl b)]) -> (op, [Ind1 (Lit (find_label labels a)); Imm (Lit (find_label labels b))])::(label_to_address is labels)
                | (op, [Imm (Lbl a); b]) -> (op, [Imm (Lit (find_label labels a)); b])::(label_to_address is labels)
                | (op, [Ind1 (Lbl a); b]) -> (op, [Ind1 (Lit (find_label labels a)); b])::(label_to_address is labels)
                | (op, [a; Imm (Lbl b)]) -> (op, [a; Imm (Lit (find_label labels b))])::(label_to_address is labels)
                | (op, [a; Ind1 (Lbl b)]) -> (op, [a; Ind1 (Lit (find_label labels b))])::(label_to_address is labels)
                | (op, [Imm (Lbl a)]) -> (op, [Imm (Lit (find_label labels a))])::(label_to_address is labels)
                | (op, [Ind1 (Lbl a)]) -> (op, [Ind1 (Lit (find_label labels a))])::(label_to_address is labels)
                | op -> i::(label_to_address is labels)
              end 
  end


let rec print_instructions (ins: ins list) : unit =
  begin match ins with
    | [] -> ()
    | i::is -> Printf.printf("Operation: %s\n") (string_of_ins i); print_instructions is
  end

let rec extract_text (elem : elem list) (labels: label_pos list): sbyte list =
    begin match elem with
      | [] -> []
      | e::es -> begin match e.asm with 
        | Text a -> (* print_instructions (label_to_address a labels); *) (ins_to_sbyte (label_to_address a labels)) @ (extract_text es labels)
        | Data a -> raise (Invalid_argument "This function must not be called with Data asm")
      end
    end


let rec check_lable_unique (lbl:lbl) (label : label_pos list) : unit = 
  begin match label with
    | [] -> ()
    | l::ls -> if (lbl = l.lbl) then raise (Redefined_sym lbl) else check_lable_unique lbl ls
  end

let rec labels_resolver (text_seg: elem list) (data_seg : elem list) (offset : int64) : label_pos list = 
  begin match text_seg, data_seg with
    | [], [] -> []
    | t::[], ds -> check_lable_unique t.lbl (labels_resolver [] ds (Int64.add offset (length_asm t.asm)));{lbl = t.lbl; lbl_pos = offset; next_seg_after_last_txt = (Int64.add offset (length_asm t.asm))}::(labels_resolver [] ds (Int64.add offset (length_asm t.asm)))
    | t::ts, _ -> check_lable_unique t.lbl (labels_resolver ts data_seg (Int64.add offset (length_asm t.asm))); {lbl = t.lbl; lbl_pos = offset; next_seg_after_last_txt = 0L}::(labels_resolver ts data_seg (Int64.add offset (length_asm t.asm)))
    | [], d::ds -> check_lable_unique d.lbl (labels_resolver [] ds (Int64.add offset (length_asm d.asm))); {lbl = d.lbl; lbl_pos = offset; next_seg_after_last_txt = 0L}::((labels_resolver [] ds (Int64.add offset (length_asm d.asm))));
  end

let rec find_first_data (labels : label_pos list) : int64 =
  begin match labels with 
    | [] -> raise (Invalid_argument "No last text segment set")
    | l::ls -> if (l.next_seg_after_last_txt <> 0L) then l.next_seg_after_last_txt else find_first_data ls 
  end
 

let rec print_labels (labels : label_pos list) : unit =
  begin match labels with
  | [] -> ()
  | l::ls -> Printf.printf("Label: %Ld\n") l.lbl_pos; print_labels ls
  end
(* 
let rec print_ins (ins : ) : unit = 
  begin match ins with
    | [] -> ()
    | i::is -> Printf.printf("Operation: %s\n") (string_of_ins i); print_ins is
      (* begin match i with 
                | Byte c -> print_ins is
                | InsFrag -> print_ins is
                | InsB0 (op, [src; dest]) -> Printf.printf("Op: %s") (string_of_opcode op); print_ins is
                | InsB0 (op, [src]) -> Printf.printf("Op %s") (string_of_opcode op); print_ins is
                | _ -> print_ins is
              end *)
  end *)

let assemble (p:prog) : exec =
  let text_seg = create_text_seg p in
    let data_seg = create_data_seg p in 
      let labels = labels_resolver text_seg data_seg 0L in
        (* print_labels labels; *)

        { entry = find_label labels "main"         (* address of the entry point *)
          ; text_pos = mem_bot         (* starting address of the code *)
          ; data_pos = (Int64.add (find_first_data labels) 0x400000L)            (* starting address of the data *)
          ; text_seg = extract_text text_seg labels     (* contents of the text segment *)
          ; data_seg = extract_data data_seg       (* contents of the data segment *)
        }



  

(* let rec add_elem (p: prog)  : unit =
  begin match p with 
    | [] -> ()
    | el::els -> add_elem (els); 
                begin match el.asm with
                  | Text a -> el::text_list
                  | Data a -> el::data_list
                end
  end *)

  (* begin match el.asm with 
    | Text a -> text_list::[|el|]
    | Data a  -> data_list::[|el|]
  end *)

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)



let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  let mem = (Array.make mem_size (Byte '\x00')) in
  Array.blit (Array.of_list text_seg) 0 mem 0 (List.length text_seg);
  Array.blit (Array.of_list data_seg) 0 mem (Int64.to_int (Int64.sub data_pos 0x400000L)) (List.length data_seg);
  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- Int64.sub mem_top 8L;

  Array.blit (Array.of_list (sbytes_of_int64 exit_addr)) 0 mem (Int64.to_int (Int64.sub mem_top 0x400008L)) 8;

  { flags = {fo = false; fs = false; fz = false};
    regs = regs;
    mem = mem
  }
