
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

(* Treat terminator as living at index length code, anything beyond that is stuck **)

Fixpoint nth_opt {A : Type} (n : nat) (xs : list A) : option A :=
  match n, xs with
  | 0, x :: _ => Some x
  | S n', _ :: xs' => nth_opt n' xs'
  | _, _ => None
  end.

Inductive fetched : Type :=
| FInstr : instr -> fetched
| FTerm  : term  -> fetched.

Definition fetch (P : prog) (p : pc) : option fetched :=
  match P (pc_lbl p) with
  | None => None
  | Some b =>
      match nth_opt (pc_ix p) (code b) with
      | Some i => Some (FInstr i)
      | None =>
          (* if we've stepped past all code, we're at the terminator *)
          if Nat.eqb (pc_ix p) (length (code b))
          then Some (FTerm (termi b))
          else None
      end
  end.


(* Fallthrough increments index, jumps set (label, 0) **)
Definition pc_next (p : pc) : pc :=
  {| pc_lbl := pc_lbl p; pc_ix := S (pc_ix p) |}.

Definition pc_jump (l : label) : pc :=
  {| pc_lbl := l; pc_ix := 0 |}.


(* change per-instruction stepping to partial executor for instr instead *)
(* Now generally does pc_next on success  *)
Definition exec_instr (s : state) (i : instr) : option state :=
  match i with
  | Nop =>
      Some {| pcv := pc_next (pcv s); rf := rf s; mm := mm s |}

  | Add rd rs1 rs2 =>
      let tv1 := rf s rs1 in
      let tv2 := rf s rs2 in
      let v := tv_val tv1 + tv_val tv2 in
      let t := t_or (tv_taint tv1) (tv_taint tv2) in
      Some {| pcv := pc_next (pcv s);
              rf  := regs_set (rf s) rd (mk_tval v t);
              mm  := mm s |}

  | Mul rd rs1 rs2 =>
      let tv1 := rf s rs1 in
      let tv2 := rf s rs2 in
      let v := tv_val tv1 * tv_val tv2 in
      let t := t_or (tv_taint tv1) (tv_taint tv2) in
      Some {| pcv := pc_next (pcv s);
              rf  := regs_set (rf s) rd (mk_tval v t);
              mm  := mm s |}

  | Load sz rd base off =>
      if tv_taint (rf s base) then None
      else
        let a := tv_val (rf s base) + off in
        match load_bytes (mm s) a (size_bytes sz) with
        | None => None
        | Some tbs =>
            let v := pack_le (tbytes_vals tbs) in
            let t := tbytes_taint tbs in
            Some {| pcv := pc_next (pcv s);
                    rf  := regs_set (rf s) rd (mk_tval v t);
                    mm  := mm s |}
        end

  | Store sz rs_val base off =>
      if tv_taint (rf s base) then None
      else
        let a := tv_val (rf s base) + off in
        let v := tv_val (rf s rs_val) in
        let t := tv_taint (rf s rs_val) in
        let bs := unpack_le v (size_bytes sz) in
        let tbs := map (fun b => mk_tbyte b t) bs in
        Some {| pcv := pc_next (pcv s);
                rf  := rf s;
                mm  := store_bytes (mm s) a tbs |}
  end.
(** ***)
  
(* terminator execution **)
Definition exec_term (s : state) (t : term) : option state :=
  match t with
  | THalt => None
  | TJmp l =>
      Some {| pcv := pc_jump l; rf := rf s; mm := mm s |}
  | TBrZero r l_then l_else =>
      if tv_taint (rf s r) then None
      else if Nat.eqb (tv_val (rf s r)) 0
           then Some {| pcv := pc_jump l_then; rf := rf s; mm := mm s |}
           else Some {| pcv := pc_jump l_else; rf := rf s; mm := mm s |}
  end.
(** ***)

(* Edit step inductive to include both instr and term **)
Inductive step (P : prog) : state -> state -> Prop :=
| StepInstr :
    forall s i s',
      fetch P (pcv s) = Some (FInstr i) ->
      exec_instr s i = Some s' ->
      step P s s'
| StepTerm :
    forall s t s',
      fetch P (pcv s) = Some (FTerm t) ->
      exec_term s t = Some s' ->
      step P s s'.
(** ***)