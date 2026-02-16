
Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool.
From Stdlib Require Import Lists.List.
Import ListNotations.
From SimpleIsa Require Import Syntax.


(* Size -> # of bytes *)
Definition size_bytes (sz : size) : nat :=
  match sz with
  | S1 => 1
  | S2 => 2
  | S4 => 4
  | S8 => 8
  end.

(* packing - unpacking *)
Fixpoint pack_le (bs : list nat) : nat :=
  match bs with
  | nil => 0
  | b :: bs' => b + 256 * pack_le bs'
  end.

Fixpoint unpack_le (n : nat) (k : nat) : list nat :=
  match k with
  | 0 => nil
  | S k' => (n mod 256) :: unpack_le (n / 256) k'
  end.

(* reading "n bytes" from memory *)
Fixpoint load_bytes (m : mem) (a : addr) (n : nat) : option (list tbyte) :=
  match n with
  | 0 => Some nil
  | S n' =>
      match m a, load_bytes m (a + 1) n' with
      | Some tb, Some tbs => Some (tb :: tbs)
      | _, _ => None
      end
  end.

(* writing bytes to memory *)
Fixpoint store_bytes (m : mem) (a : addr) (tbs : list tbyte) : mem :=
  match tbs with 
  | nil => m
  | tb :: tbs' => store_bytes (mem_set m a tb) (a + 1) tbs'
  end.

(* taints accross bytes *)
Fixpoint taint_or_list (ts : list taint) : taint :=
  match ts with
  | nil => false
  | t :: ts' => t_or t (taint_or_list ts')
  end.

Definition tbytes_taint (tbs : list tbyte) : taint :=
  taint_or_list (map tb_taint tbs).

Definition tbytes_vals (tbs : list tbyte) : list nat :=
  map tb_val tbs.

(** ***)

(* change per-instruction stepping to partial executor for instr instead *)
Definition exec_instr (s : state) (i : instr) : option state :=
  match i with
  | Nop => Some s

  | Add rd rs1 rs2 =>
      let tv1 := rf s rs1 in 
      let tv2 := rf s rs2 in
      let v := tv_val tv1 + tv_val tv2 in
      let t := t_or (tv_taint tv1) (tv_taint tv2) in
      Some {| pc := pc s;
              rf := regs_set (rf s) rd (mk_tval v t);
              mm := mm s|}
  
  | Mul rd rs1 rs2 =>
      let tv1 := rf s rs1 in 
      let tv2 := rf s rs2 in
      let v := tv_val tv1 * tv_val tv2 in
      let t := t_or (tv_taint tv1) (tv_taint tv2) in
      Some {| pc := pc s;
              rf := regs_set (rf s) rd (mk_tval v t);
              mm := mm s|}

  | Load sz rd base off =>
      if tv_taint (rf s base) then None
      else
        let a := tv_val (rf s base) + off in
        match load_bytes (mm s) a (size_bytes sz) with
        | None => None
        | Some tbs =>
            let v := pack_le (tbytes_vals tbs) in
            let t := tbytes_taint tbs in
            Some {| pc := pc s;
                    rf := regs_set (rf s) rd (mk_tval v t);
                    mm := mm s |}
        end
  
  | Store sz rs_val base off =>
      if tv_taint (rf s base) then None
      else 
        let a := tv_val (rf s base) + off in
        let v := tv_val (rf s rs_val) in
        let t := tv_taint (rf s rs_val) in 
        let bs := unpack_le v (size_bytes sz) in 
        let tbs := map (fun b => mk_tbyte b t) bs in
        Some {| pc := pc s;
                rf := rf s; 
                mm := store_bytes (mm s) a tbs |}
    end.
(** ***)

(* running the list, if some instruction gets stuck the whole block does **)
Fixpoint exec_code (s : state) (c : list instr) : option state :=
    match c with
    | nil => Some s
    | i :: c' =>
        match exec_instr s i with
        | None => None
        | Some s' => exec_code s' c'
        end
    end.
(** ***)
  
(* terminator execution **)
Definition exec_term (s : state) (t : term) : option state :=
  match t with
  | THalt => None (* if condition reg tainted, get stuck **)
  | TJmp l => 
      Some {| pc := l; rf := rf s; mm := mm s|}
  | TBrZero r l_then l_else => (* if explicit tainted/not tainted, l_then l_else*)
      if tv_taint (rf s r) then None
      else if Nat.eqb (tv_val (rf s r)) 0
          then Some {| pc := l_then; rf := rf s; mm := mm s|}
          else Some {| pc := l_else; rf := rf s; mm := mm s|}
  end.
(** ***)

(* new step inductive to execute one block*)
Inductive step (P : prog) : state -> state -> Prop :=
| StepBlock :
    forall s b s_mid s',
      P (pc s) = Some b ->
      exec_code s (code b) = Some s_mid ->
      exec_term s_mid (termi b) = Some s' ->
      step P s s'.
(** ***)

