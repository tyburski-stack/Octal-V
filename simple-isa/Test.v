Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool Lia Lists.List.
Import ListNotations.
From SimpleIsa Require Import Syntax Machine Safety Typing.

(* ===================================================================== *)
(* Checkpoint C2: a positive program that types and runs, and a negative *)
(* program (branch on a value loaded from memory, hence possibly secret) *)
(* that provably has NO typing derivation for ANY choice of block entry  *)
(* types.                                                                *)
(* ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* Positive example                                                    *)
(*                                                                     *)
(* Register 1 holds a secret.  Block 0 computes r0 := r1 + r2 (so r0   *)
(* becomes secret), then jumps to block 1, which halts.                *)
(* ------------------------------------------------------------------ *)

Definition blk0 : block := {| code := [Add 0 1 2]; termi := TJmp 1 |}.
Definition blk1 : block := {| code := []; termi := THalt |}.

Definition Pgood : prog :=
  fun l =>
    match l with
    | 0 => Some blk0
    | 1 => Some blk1
    | _ => None
    end.

(* Entry types: at block 0, r1 is secret and everything else public.
   Block 1 accepts anything (all registers may be secret). *)
Definition sec_r1 : sty := fun r => Nat.eqb r 1.
Definition top : sty := fun _ => true.

Definition Tgood : label -> sty :=
  fun l => match l with 0 => sec_r1 | _ => top end.

Lemma Pgood_typed : program_typed Pgood Tgood.
Proof.
  intros l b Hb.
  destruct l as [| [| l]]; simpl in Hb; inversion Hb; subst; clear Hb.
  - (* block 0 *)
    eexists. split.
    + eapply ITCons; [apply TyAdd | apply ITNil].
    + eapply TyJmp; [reflexivity |].
      intros r _. reflexivity.
  - (* block 1 *)
    eexists. split; [apply ITNil | apply TyHalt].
Qed.

(* An initial state: pc at block 0, r1 = (7, secret), all other
   registers (0, public); memory totally defined and public. *)
Definition rf0 : regs :=
  fun r => if Nat.eqb r 1 then mk_tval 7 true else mk_tval 0 false.
Definition mm0 : mem := fun _ => Some (mk_tbyte 0 false).
Definition s0 : state := {| pcv := pc_jump 0; rf := rf0; mm := mm0 |}.

Lemma s0_wf : wf_state Pgood (gamma_of Pgood Tgood) s0.
Proof.
  eapply typed_start_wf with (l := 0) (b := blk0).
  - exact Pgood_typed.
  - reflexivity.
  - reflexivity.
  - intros a. eexists. reflexivity.
  - intros r Hr. unfold Tgood, sec_r1 in Hr. simpl.
    unfold rf0. rewrite Hr. reflexivity.
Qed.

(* The positive program actually runs: two steps, then a terminal
   (halting) state. *)
Lemma good_runs :
  exists s1 s2,
    step Pgood s0 s1 /\ step Pgood s1 s2 /\ terminal Pgood s2.
Proof.
  eexists. eexists.
  split; [| split].
  - eapply StepInstr; reflexivity.
  - eapply StepTerm; reflexivity.
  - reflexivity.
Qed.

(* And type safety applies to it with zero assumptions. *)
Corollary good_safe :
  (exists s', step Pgood s0 s' /\ wf_state Pgood (gamma_of Pgood Tgood) s')
  \/ terminal Pgood s0.
Proof.
  apply typed_type_safety; [exact Pgood_typed | exact s0_wf].
Qed.

(* ------------------------------------------------------------------ *)
(* Negative example                                                    *)
(*                                                                     *)
(* Block 0 loads a byte from memory into r0 (which the Phase-1 type    *)
(* system must treat as possibly secret, since there is no memory      *)
(* model), then BRANCHES on r0.  Branching on a secret leaks it, so    *)
(* this program must not type — for ANY assignment of block entry      *)
(* types.                                                              *)
(* ------------------------------------------------------------------ *)

Definition blkbad : block :=
  {| code := [Load S1 0 1 0]; termi := TBrZero 0 1 1 |}.

Definition Pbad : prog :=
  fun l =>
    match l with
    | 0 => Some blkbad
    | 1 => Some blk1
    | _ => None
    end.

Theorem Pbad_untypeable :
  forall Θ : label -> sty, ~ program_typed Pbad Θ.
Proof.
  intros Θ H.
  specialize (H 0 blkbad eq_refl).
  destruct H as (R_end & Hchain & Htm).
  (* Invert the chain: the Load forces r0 := may-be-secret. *)
  inversion Hchain as [| R0 i R1 l0 R2 Hi Hrest]; subst.
  inversion Hi; subst.
  inversion Hrest; subst.
  (* Now R_end = sty_set (Θ 0) 0 true; the branch needs R_end 0 = false. *)
  inversion Htm; subst.
  assert (Htrue : sty_set (Θ 0) 0 true 0 = true) by reflexivity.
  congruence.
Qed.

(* Note the operational counterpart: if the loaded byte is actually
   tainted, the machine itself refuses to branch on it (exec_term
   returns None), i.e. the negative program can get dynamically stuck —
   exactly the situation the type system rejects statically. *)
Example bad_gets_stuck :
  (* run Pbad from a state whose memory holds a secret byte at the
     load address: after the Load, the branch is stuck *)
  let rfb : regs := fun _ => mk_tval 0 false in
  let mmb : mem := fun _ => Some (mk_tbyte 1 true) in
  let sb : state := {| pcv := pc_jump 0; rf := rfb; mm := mmb |} in
  exists s1,
    step Pbad sb s1 /\
    ~ terminal Pbad s1 /\
    forall s2, ~ step Pbad s1 s2.
Proof.
  intros rfb mmb sb.
  eexists. split; [| split].
  - eapply StepInstr; reflexivity.
  - unfold terminal. simpl. intros H. inversion H.
  - intros s2 Hst.
    inversion Hst as [s i s2' Hf Hex | s t s2' Hf Hex]; subst;
      simpl in Hf; inversion Hf; subst; simpl in Hex; discriminate.
Qed.
