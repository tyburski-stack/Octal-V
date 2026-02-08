
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


(* updated step/load rules for bytes *)

Inductive step (P : prog) : state -> state -> Prop :=
| StepNop :
    forall s,
      P (pc s) = Some Nop ->
      step P s {| pc := pc s + 1; rf := rf s; mm := mm s |}

| StepAdd :
    forall s rd rs1 rs2,
      P (pc s) = Some (Add rd rs1 rs2) ->
      let tv1 := rf s rs1 in 
      let tv2 := rf s rs2 in
      let v := tv_val tv1 + tv_val tv2 in
      let t := t_or (tv_taint tv1) (tv_taint tv2) in
      step P s {| pc := pc s + 1;
                  rf := regs_set (rf s) rd (mk_tval v t);
                  mm := mm s|}

| StepMul :
    forall s rd rs1 rs2,
      P (pc s) = Some (Mul rd rs1 rs2) ->
        let tv1 := rf s rs1 in 
        let tv2 := rf s rs2 in
        let v := tv_val tv1 * tv_val tv2 in
        let t := t_or (tv_taint tv1) (tv_taint tv2) in
        step P s {| pc := pc s + 1;
                    rf := regs_set (rf s) rd (mk_tval v t);
                    mm := mm s|}

(* Load updated *)
| StepLoad :
    forall s sz rd base off a tbs,
      P (pc s) = Some (Load sz rd base off) ->
      tv_taint (rf s base) = false ->
      a = tv_val (rf s base) + off ->
      load_bytes (mm s) a (size_bytes sz) = Some tbs ->
      let v := pack_le (tbytes_vals tbs) in
      let t := tbytes_taint tbs in
      step P s {| pc := pc s + 1;
                  rf := regs_set (rf s) rd (mk_tval v t);
                  mm := mm s |}

(* Store updated *)
| StepStore :
    forall s sz rs_val base off a,
      P (pc s) = Some (Store sz rs_val base off) ->
      tv_taint (rf s base) = false ->
      a = tv_val (rf s base) + off ->
      let v := tv_val (rf s rs_val) in
      let t := tv_taint (rf s rs_val) in 
      let bs := unpack_le v (size_bytes sz) in 
      let tbs := map (fun b => mk_tbyte b t) bs in
      step P s {| pc := pc s + 1;
                  rf := rf s; 
                  mm := store_bytes (mm s) a tbs |}

| StepBrZeroTaken :
    forall s rs off,
      P (pc s) = Some (BrZero rs off) ->
      tv_taint (rf s rs) = false ->
      tv_val (rf s rs) = 0 ->
      step P s {| pc := pc s + 1 + off; rf := rf s; mm := mm s |}

| StepBrZeroNotTaken :
    forall s rs off,
      P (pc s) = Some (BrZero rs off) ->
      tv_taint (rf s rs) = false ->
      tv_val (rf s rs) <> 0 ->
      step P s {| pc := pc s + 1; rf := rf s; mm := mm s |}. 