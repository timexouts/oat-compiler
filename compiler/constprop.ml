open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)

let op_lbl_helper (id : string) (d: fact): SymConst.t =
  let res = UidM.find_opt id d in
  begin match res with
    | None -> SymConst.UndefConst
    | Some x -> x
  end
let op_helper (op:operand) (d: fact): SymConst.t =
  begin match op with
    | Const x -> SymConst.Const x
    | Null -> SymConst.UndefConst
    | Gid id | Id id -> op_lbl_helper id d
  end
let binop_helper (b: bop) (i: int64) (j: int64) : int64 =
  begin match b with
    | Add -> Int64.add i j
    | Sub -> Int64.sub i j
    | Mul -> Int64.mul i j
    | Shl -> Int64.shift_left i (Int64.to_int j)
    | Lshr -> Int64.shift_right_logical i (Int64.to_int j)
    | Ashr -> Int64.shift_right i (Int64.to_int j)
    | And -> Int64.logand i j
    | Or -> Int64.logor i j
    | Xor -> Int64.logxor i j
  end

let icmp_helper (c:cnd) (i: int64) (j: int64) : int64 = (* might be wrong return type*)
  let res = begin match c with
    | Eq -> i = j
    | Ne -> i <> j
    | Slt -> i < j
    | Sle -> i <= j
    | Sgt -> i > j
    | Sge -> i >= j
  end
  in
  if res then 1L else 0L

let insn_flow (u,i:uid * insn) (d:fact) : fact =
  begin match i with 
    | Binop (b,t, op1, op2) -> 
        let op1_res = op_helper op1 d in
        let op2_res = op_helper op2 d in
        begin match op1_res, op2_res with
          | SymConst.Const l, SymConst.Const j -> UidM.add u (SymConst.Const (binop_helper b l j)) d
          | SymConst.UndefConst, _ | _, SymConst.UndefConst -> UidM.add u SymConst.UndefConst d
          | SymConst.NonConst, _ | _, SymConst.NonConst -> UidM.add u SymConst.NonConst d
        end
    
    | Icmp (c, t, op1, op2) ->
        let op1_res = op_helper op1 d in
        let op2_res = op_helper op2 d in
        begin match op1_res, op2_res with
          | SymConst.Const l, SymConst.Const j -> UidM.add u (SymConst.Const (icmp_helper c l j)) d
          | SymConst.UndefConst, _ | _, SymConst.UndefConst -> UidM.add u SymConst.UndefConst d
          | SymConst.NonConst, _ | _, SymConst.NonConst -> UidM.add u SymConst.NonConst d
        end

    | Store (_, _, _) | Call (Void, _, _) -> UidM.add u SymConst.UndefConst d
    | _ -> UidM.add u SymConst.NonConst d
  end


(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)


    let combine_facts (f1:SymConst.t) (f2:SymConst.t) : SymConst.t = (*Important: might be incorrect  *)
      begin match f1, f2 with
        | SymConst.Const x, SymConst.Const y -> if x = y then SymConst.Const x else SymConst.NonConst
        | SymConst.Const x, SymConst.UndefConst -> Const x
        | SymConst.UndefConst, SymConst.Const y -> Const y
        | SymConst.NonConst, _ | _, SymConst.NonConst -> SymConst.NonConst
        | _ -> SymConst.UndefConst
      end

    let rec combine_helper (ds:fact list) : fact = (*Important: might be incorrect*)
      begin match ds with
        | [] -> UidM.empty
        | f::fs -> UidM.merge (fun combine_facts f1 f2-> 
          begin match f1, f2 with
            | Some x, Some y ->  begin match x, y with
            | SymConst.Const x, SymConst.Const y -> if x = y then Some (SymConst.Const x) else Some SymConst.NonConst
            | SymConst.Const x, SymConst.UndefConst -> Some (Const x)
            | SymConst.UndefConst, SymConst.Const y -> Some(Const y)
            | SymConst.NonConst, _ | _, SymConst.NonConst -> Some (SymConst.NonConst)
            | _ -> Some SymConst.UndefConst
          end
            | None, Some y -> Some y
            | Some x, None -> Some x
          end
        ) f (combine_helper fs)
      end

    let combine (ds:fact list) : fact =
      combine_helper ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.*)

let resolve_operand (op:Ll.operand) (fact:fact) : Ll.operand =
  begin match op with
    | Gid id | Id id -> 
      begin match UidM.find_opt id fact with
      | Some (Const i) -> Const i
      | _ -> op
      end
    | _ -> op
  end

let resolve_term ((uid, arnold) : Ll.uid * Ll.terminator) (uid_out : uid -> 'd) : (Ll.uid * Ll.terminator) = (*Arnold aka terminator - sorry for that*)
  let fact = uid_out uid in
  begin match arnold with
    | Ret (t, op) -> 
        begin match op with
          | None -> (uid, Ret (t, None))
          | Some in_op -> (uid, Ret (t, Some (resolve_operand in_op fact)))
          end
    | Br l -> (uid, Br l)
    | Cbr (op, l1, l2) -> (uid, Cbr (resolve_operand op fact, l1, l2))
  end

let resolve_ins ((uid, ins): Ll.uid * Ll.insn) (uid_out : uid -> 'd) : (Ll.uid * Ll.insn)  =
  let fact = uid_out uid in
  begin match ins with
    | Binop (b, t, op1, op2) -> (uid, Binop (b, t, resolve_operand op1 fact, resolve_operand op2 fact))
    | Alloca t -> (uid, Alloca t)
    | Load (t, op) -> (uid, Load (t, resolve_operand op fact))
    | Store (t, op1, op2) -> (uid, Store (t, resolve_operand op1 fact, resolve_operand op2 fact))
    | Icmp (c, t, op1, op2) -> (uid, Icmp (c, t, resolve_operand op1 fact, resolve_operand op2 fact))
    | Call (t, op, ty_op_ls) -> (uid, Call (t, resolve_operand op fact, List.map (fun (t_inner, op_inner) -> (t_inner, resolve_operand op_inner fact)) ty_op_ls))
    | Bitcast (t1, op, t2) -> (uid, Bitcast (t1, resolve_operand op fact, t2))
    | Gep (t, op, op_ls) -> (uid, Gep (t, resolve_operand op fact, List.map (fun op_inner -> resolve_operand op_inner fact) op_ls))
  end



let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in (*first block*)
    let cb = Graph.uid_out cg l in (*labels of the out blocks of block b*)
    let new_insns = List.map (fun (uid, ins) -> resolve_ins (uid, ins) cb) b.insns in
    let new_term = resolve_term b.term cb in
    let new_block = {insns = new_insns; term = new_term} in
    {cfg with blocks = LblM.add l new_block (LblM.remove l cfg.blocks)} 

  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
