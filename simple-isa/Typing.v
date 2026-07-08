Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool Lia Lists.List.
Import ListNotations.
From SimpleIsa Require Import Syntax Machine Safety.

(* ===================================================================== *)
(* Phase 1 (Checkpoint C1): concrete register-taint typing instantiating *)
(* the abstract tyenv layer of Safety.v.                                 *)
(*                                                                       *)
(* A state type assigns each register a taint bound:                     *)
(*   true  = "may be secret"                                             *)
(*   false = "definitely public"                                         *)
(*                                                                       *)
(* Typing is per program point (pc = label * index).  Block typing is    *)
(* relational: an inductive chain [instrs_ty] threads a state type       *)
(* through the code list of a block, ending in a terminator typing.      *)
(* The concrete tyenv [gamma_of] asserts, at point (l, ix), that the     *)
(* REMAINING code (skipn ix) of the block, followed by its terminator,   *)
(* is well-typed from a state type the current state satisfies.  This    *)
(* makes preservation a direct inversion of the typing chain.            *)
(* ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* State types                                                         *)
(* ------------------------------------------------------------------ *)

Definition sty := reg -> taint.

Definition sty_set (R : sty) (x : reg) (t : taint) : sty :=
  fun y => if Nat.eqb y x then t else R y.

(* A register file satisfies R when every register typed public is
   dynamically untainted. *)
Definition state_satisfies (R : sty) (s : state) : Prop :=
  forall r, R r = false -> tv_taint (rf s r) = false.

(* Subtyping / weakening: R1 <: R2 when R2 is at least as secret. *)
Definition sty_sub (R1 R2 : sty) : Prop :=
  forall r, R1 r = true -> R2 r = true.

Lemma sty_sub_refl : forall R, sty_sub R R.
Proof. intros R r H; exact H. Qed.

Lemma state_satisfies_sub :
  forall R1 R2 s, sty_sub R1 R2 -> state_satisfies R1 s -> state_satisfies R2 s.
Proof.
  intros R1 R2 s Hsub Hsat r Hr2.
  destruct (R1 r) eqn:E1.
  - apply Hsub in E1. congruence.
  - apply Hsat. exact E1.
Qed.

(* ------------------------------------------------------------------ *)
(* Memory totality invariant: every address is defined.  This makes    *)
(* Load definedness hold in Phase 1, where there is no memory model.   *)
(* ------------------------------------------------------------------ *)

Definition mem_total (m : mem) : Prop :=
  forall a, exists tb, m a = Some tb.

Lemma mem_set_total :
  forall m a tb, mem_total m -> mem_total (mem_set m a tb).
Proof.
  intros m a tb H x. unfold mem_set.
  destruct (Nat.eqb x a).
  - eexists; reflexivity.
  - apply H.
Qed.

Lemma store_bytes_total :
  forall tbs m a, mem_total m -> mem_total (store_bytes m a tbs).
Proof.
  induction tbs as [| tb tbs IH]; intros m a H; simpl.
  - exact H.
  - apply IH. apply mem_set_total. exact H.
Qed.

Lemma load_bytes_total :
  forall n m a, mem_total m -> exists tbs, load_bytes m a n = Some tbs.
Proof.
  induction n as [| n IH]; intros m a H; simpl.
  - eexists; reflexivity.
  - destruct (H a) as [tb Htb]. rewrite Htb.
    destruct (IH m (a + 1) H) as [tbs Htbs]. rewrite Htbs.
    eexists; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Facts about nth_opt / skipn                                         *)
(* ------------------------------------------------------------------ *)

Lemma nth_opt_some_lt :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    nth_opt n l = Some x -> n < length l.
Proof.
  intros A n; induction n as [| n IH]; intros l x H;
    destruct l as [| y l]; simpl in H; try discriminate.
  - simpl. lia.
  - apply IH in H. simpl. lia.
Qed.

Lemma nth_opt_none_ge :
  forall (A : Type) (n : nat) (l : list A),
    nth_opt n l = None -> length l <= n.
Proof.
  intros A n; induction n as [| n IH]; intros l H;
    destruct l as [| y l]; simpl in *; try discriminate; try lia.
  apply IH in H. lia.
Qed.

Lemma skipn_nth_some :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    nth_opt n l = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
  intros A n; induction n as [| n IH]; intros l x H;
    destruct l as [| y l]; simpl in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Typing rules                                                        *)
(* ------------------------------------------------------------------ *)

Inductive instr_ty : sty -> instr -> sty -> Prop :=
| TyNop : forall R,
    instr_ty R Nop R
| TyAdd : forall R rd rs1 rs2,
    instr_ty R (Add rd rs1 rs2) (sty_set R rd (t_or (R rs1) (R rs2)))
| TyMul : forall R rd rs1 rs2,
    instr_ty R (Mul rd rs1 rs2) (sty_set R rd (t_or (R rs1) (R rs2)))
| TyLoad : forall R sz rd base off,
    R base = false ->                       (* address must be public *)
    instr_ty R (Load sz rd base off) (sty_set R rd true)
                                            (* no memory model yet:
                                               loaded value may be secret *)
| TyStore : forall R sz rs base off,
    R base = false ->                       (* address must be public *)
    instr_ty R (Store sz rs base off) R.

(* Terminator typing.  Branch targets must exist and their entry types
   must be weaker than the current state type. *)
Inductive term_ty (P : prog) (Θ : label -> sty) : sty -> term -> Prop :=
| TyHalt : forall R,
    term_ty P Θ R THalt
| TyJmp : forall R l b,
    P l = Some b ->
    sty_sub R (Θ l) ->
    term_ty P Θ R (TJmp l)
| TyBrZero : forall R r l1 l2 b1 b2,
    R r = false ->                          (* branch condition public *)
    P l1 = Some b1 ->
    P l2 = Some b2 ->
    sty_sub R (Θ l1) ->
    sty_sub R (Θ l2) ->
    term_ty P Θ R (TBrZero r l1 l2).

(* Relational typing of an instruction sequence. *)
Inductive instrs_ty : sty -> list instr -> sty -> Prop :=
| ITNil : forall R,
    instrs_ty R [] R
| ITCons : forall R i R' l R'',
    instr_ty R i R' ->
    instrs_ty R' l R'' ->
    instrs_ty R (i :: l) R''.

Definition block_ty (P : prog) (Θ : label -> sty) (R : sty) (b : block) : Prop :=
  exists R_end,
    instrs_ty R (code b) R_end /\ term_ty P Θ R_end (termi b).

Definition program_typed (P : prog) (Θ : label -> sty) : Prop :=
  forall l b, P l = Some b -> block_ty P Θ (Θ l) b.

(* ------------------------------------------------------------------ *)
(* The concrete tyenv                                                  *)
(* ------------------------------------------------------------------ *)

(* R is a valid type for program point p: the remaining code of the
   block at p, followed by the terminator, types from R. *)
Definition point_ok (P : prog) (Θ : label -> sty) (p : pc) (R : sty) : Prop :=
  exists b,
    P (pc_lbl p) = Some b /\
    pc_ix p <= length (code b) /\
    exists R_end,
      instrs_ty R (skipn (pc_ix p) (code b)) R_end /\
      term_ty P Θ R_end (termi b).

Definition gamma_of (P : prog) (Θ : label -> sty) : tyenv :=
  fun p s =>
    mem_total (mm s) /\
    exists R, point_ok P Θ p R /\ state_satisfies R s.

(* ------------------------------------------------------------------ *)
(* Progress lemmas: typing + satisfaction imply executability          *)
(* ------------------------------------------------------------------ *)

Lemma instr_ty_progress :
  forall R i R' s,
    instr_ty R i R' ->
    state_satisfies R s ->
    mem_total (mm s) ->
    instr_safe s i.
Proof.
  intros R i R' s Hty Hsat Htot.
  unfold instr_safe.
  destruct Hty; simpl.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - (* Load *)
    rewrite (Hsat base H).
    destruct (load_bytes_total (size_bytes sz) (mm s)
                (tv_val (rf s base) + off) Htot) as [tbs Hl].
    rewrite Hl. eexists; reflexivity.
  - (* Store *)
    rewrite (Hsat base H). eexists; reflexivity.
Qed.

Lemma term_ty_progress :
  forall P Θ R t s,
    term_ty P Θ R t ->
    state_satisfies R s ->
    term_safe s t.
Proof.
  intros P Θ R t s Hty Hsat.
  destruct Hty.
  - left; reflexivity.
  - right; eexists; reflexivity.
  - right. simpl. rewrite (Hsat r H).
    destruct (Nat.eqb (tv_val (rf s r)) 0); eexists; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Preservation lemmas                                                 *)
(* ------------------------------------------------------------------ *)

Lemma exec_instr_pc :
  forall s i s',
    exec_instr s i = Some s' -> pcv s' = pc_next (pcv s).
Proof.
  intros s i s' H.
  destruct i as [| rd rs1 rs2 | rd rs1 rs2 | sz rd base off | sz rs base off];
    simpl in H.
  - injection H as <-; reflexivity.
  - injection H as <-; reflexivity.
  - injection H as <-; reflexivity.
  - destruct (tv_taint (rf s base)); [discriminate|].
    destruct (load_bytes (mm s) (tv_val (rf s base) + off) (size_bytes sz));
      [| discriminate].
    injection H as <-; reflexivity.
  - destruct (tv_taint (rf s base)); [discriminate|].
    injection H as <-; reflexivity.
Qed.

Lemma exec_instr_mem :
  forall s i s',
    exec_instr s i = Some s' -> mem_total (mm s) -> mem_total (mm s').
Proof.
  intros s i s' H Htot.
  destruct i as [| rd rs1 rs2 | rd rs1 rs2 | sz rd base off | sz rs base off];
    simpl in H.
  - injection H as <-; exact Htot.
  - injection H as <-; exact Htot.
  - injection H as <-; exact Htot.
  - destruct (tv_taint (rf s base)); [discriminate|].
    destruct (load_bytes (mm s) (tv_val (rf s base) + off) (size_bytes sz));
      [| discriminate].
    injection H as <-; exact Htot.
  - destruct (tv_taint (rf s base)); [discriminate|].
    injection H as <-. simpl. apply store_bytes_total. exact Htot.
Qed.

Lemma instr_ty_preserves_sat :
  forall R i R' s s',
    instr_ty R i R' ->
    state_satisfies R s ->
    exec_instr s i = Some s' ->
    state_satisfies R' s'.
Proof.
  intros R i R' s s' Hty Hsat Hex.
  destruct Hty; simpl in Hex.
  - (* Nop *)
    injection Hex as <-. intros r Hr. simpl. apply Hsat; exact Hr.
  - (* Add *)
    injection Hex as <-. intros r Hr.
    unfold sty_set in Hr. simpl. unfold regs_set.
    destruct (Nat.eqb r rd) eqn:E.
    + unfold t_or in Hr. apply Bool.orb_false_iff in Hr.
      destruct Hr as [H1 H2].
      simpl. unfold t_or.
      rewrite (Hsat rs1 H1), (Hsat rs2 H2). reflexivity.
    + apply Hsat; exact Hr.
  - (* Mul *)
    injection Hex as <-. intros r Hr.
    unfold sty_set in Hr. simpl. unfold regs_set.
    destruct (Nat.eqb r rd) eqn:E.
    + unfold t_or in Hr. apply Bool.orb_false_iff in Hr.
      destruct Hr as [H1 H2].
      simpl. unfold t_or.
      rewrite (Hsat rs1 H1), (Hsat rs2 H2). reflexivity.
    + apply Hsat; exact Hr.
  - (* Load *)
    destruct (tv_taint (rf s base)); [discriminate|].
    destruct (load_bytes (mm s) (tv_val (rf s base) + off) (size_bytes sz));
      [| discriminate].
    injection Hex as <-. intros r Hr.
    unfold sty_set in Hr. simpl. unfold regs_set.
    destruct (Nat.eqb r rd) eqn:E.
    + discriminate.
    + apply Hsat; exact Hr.
  - (* Store *)
    destruct (tv_taint (rf s base)); [discriminate|].
    injection Hex as <-. intros r Hr. simpl. apply Hsat; exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* Fetch characterization                                              *)
(* ------------------------------------------------------------------ *)

Lemma fetch_inv_instr :
  forall P p b i,
    P (pc_lbl p) = Some b ->
    fetch P p = Some (FInstr i) ->
    nth_opt (pc_ix p) (code b) = Some i.
Proof.
  intros P p b i Hb Hf.
  unfold fetch in Hf. rewrite Hb in Hf.
  destruct (nth_opt (pc_ix p) (code b)) as [i0 |] eqn:E.
  - inversion Hf; subst. reflexivity.
  - destruct (Nat.eqb (pc_ix p) (length (code b))); inversion Hf.
Qed.

Lemma fetch_inv_term :
  forall P p b t,
    P (pc_lbl p) = Some b ->
    fetch P p = Some (FTerm t) ->
    t = termi b /\ pc_ix p = length (code b).
Proof.
  intros P p b t Hb Hf.
  unfold fetch in Hf. rewrite Hb in Hf.
  destruct (nth_opt (pc_ix p) (code b)) as [i0 |] eqn:E.
  - inversion Hf.
  - destruct (Nat.eqb (pc_ix p) (length (code b))) eqn:Elen.
    + inversion Hf; subst. split; [reflexivity|].
      apply Nat.eqb_eq. exact Elen.
    + inversion Hf.
Qed.

(* ------------------------------------------------------------------ *)
(* From Γ to full well-formedness (Γ + safety of the next fetch)       *)
(* ------------------------------------------------------------------ *)

Lemma gamma_wf_state :
  forall P Θ s,
    program_typed P Θ ->
    gamma_of P Θ (pcv s) s ->
    wf_state P (gamma_of P Θ) s.
Proof.
  intros P Θ s HPT Hg.
  split; [exact Hg |].
  destruct Hg as (Htot & R & Hpt & Hsat).
  destruct Hpt as (b & Hb & Hix & R_end & Hchain & Htm).
  destruct (nth_opt (pc_ix (pcv s)) (code b)) as [i |] eqn:E.
  - (* an instruction is next *)
    assert (Hf : fetch P (pcv s) = Some (FInstr i)).
    { unfold fetch. rewrite Hb, E. reflexivity. }
    rewrite Hf.
    rewrite (skipn_nth_some _ _ _ _ E) in Hchain.
    inversion Hchain as [| R0 i0 R' l0 R''0 Hi Hrest]; subst.
    eapply instr_ty_progress; eauto.
  - (* the terminator is next *)
    assert (Hlen : pc_ix (pcv s) = length (code b)).
    { apply nth_opt_none_ge in E. lia. }
    assert (Hf : fetch P (pcv s) = Some (FTerm (termi b))).
    { unfold fetch. rewrite Hb, E, Hlen, Nat.eqb_refl. reflexivity. }
    rewrite Hf.
    rewrite Hlen in Hchain. rewrite skipn_all in Hchain.
    inversion Hchain; subst.
    eapply term_ty_progress; eauto.
Qed.

(* Inversion helpers for terminator typing (kept as lemmas so the main
   proofs do not depend on inversion-generated hypothesis names). *)

Lemma term_ty_jmp_inv :
  forall P Θ R l,
    term_ty P Θ R (TJmp l) ->
    exists b, P l = Some b /\ sty_sub R (Θ l).
Proof.
  intros P Θ R l H. inversion H; subst. eauto.
Qed.

Lemma term_ty_br_inv :
  forall P Θ R r l1 l2,
    term_ty P Θ R (TBrZero r l1 l2) ->
    R r = false /\
    (exists b1, P l1 = Some b1) /\
    (exists b2, P l2 = Some b2) /\
    sty_sub R (Θ l1) /\ sty_sub R (Θ l2).
Proof.
  intros P Θ R r l1 l2 H. inversion H; subst. eauto 8.
Qed.

(* ------------------------------------------------------------------ *)
(* Γ is preserved by steps                                             *)
(* ------------------------------------------------------------------ *)

Lemma gamma_preserved :
  forall P Θ s s',
    program_typed P Θ ->
    gamma_of P Θ (pcv s) s ->
    step P s s' ->
    gamma_of P Θ (pcv s') s'.
Proof.
  intros P Θ s s' HPT Hg Hstep.
  destruct Hg as (Htot & R & (b & Hb & Hix & R_end & Hchain & Htm) & Hsat).
  inversion Hstep as [s0 i s1 Hf Hex | s0 t s1 Hf Hex]; subst.
  - (* instruction step *)
    pose proof (fetch_inv_instr _ _ _ _ Hb Hf) as Hnth.
    rewrite (skipn_nth_some _ _ _ _ Hnth) in Hchain.
    inversion Hchain as [| R0 i0 R' l0 R''0 Hi Hrest]; subst.
    assert (Hpc : pcv s' = pc_next (pcv s)) by (eapply exec_instr_pc; eauto).
    split.
    + eapply exec_instr_mem; eauto.
    + exists R'. split.
      * exists b. rewrite Hpc. simpl. split; [exact Hb |]. split.
        { apply nth_opt_some_lt in Hnth. lia. }
        exists R_end. split; [exact Hrest | exact Htm].
      * eapply instr_ty_preserves_sat; eauto.
  - (* terminator step *)
    destruct (fetch_inv_term _ _ _ _ Hb Hf) as [Ht Hlen].
    rewrite Hlen in Hchain. rewrite skipn_all in Hchain.
    inversion Hchain; subst.
    (* Htm : term_ty P Θ R (termi b); the substitution above replaced
       t by termi b in Hex as well.  Abstract over the terminator. *)
    revert Htm Hex.
    generalize (termi b).
    intros tb Htm Hex.
    destruct tb as [l' | rr l1 l2 |].
    + (* TJmp l' *)
      apply term_ty_jmp_inv in Htm.
      destruct Htm as (b' & Hb' & Hsub).
      simpl in Hex. injection Hex as <-.
      split; [exact Htot |].
      exists (Θ l'). split.
      * exists b'. simpl. split; [exact Hb' |]. split; [lia |].
        destruct (HPT l' b' Hb') as (R_end' & Hchain' & Htm').
        exists R_end'. split; [exact Hchain' | exact Htm'].
      * intros r Hr. simpl.
        apply (state_satisfies_sub _ _ s Hsub Hsat). exact Hr.
    + (* TBrZero *)
      apply term_ty_br_inv in Htm.
      destruct Htm as (Hrr & (b1 & Hb1) & (b2 & Hb2) & Hsub1 & Hsub2).
      simpl in Hex.
      rewrite (Hsat rr Hrr) in Hex.
      destruct (Nat.eqb (tv_val (rf s rr)) 0) eqn:Ez;
        injection Hex as <-.
      * (* branch to l1 *)
        split; [exact Htot |].
        exists (Θ l1). split.
        -- exists b1. simpl. split; [exact Hb1 |]. split; [lia |].
           destruct (HPT l1 b1 Hb1) as (R_end' & Hchain' & Htm').
           exists R_end'. split; [exact Hchain' | exact Htm'].
        -- intros r Hr. simpl.
           apply (state_satisfies_sub _ _ s Hsub1 Hsat). exact Hr.
      * (* branch to l2 *)
        split; [exact Htot |].
        exists (Θ l2). split.
        -- exists b2. simpl. split; [exact Hb2 |]. split; [lia |].
           destruct (HPT l2 b2 Hb2) as (R_end' & Hchain' & Htm').
           exists R_end'. split; [exact Hchain' | exact Htm'].
        -- intros r Hr. simpl.
           apply (state_satisfies_sub _ _ s Hsub2 Hsat). exact Hr.
    + (* THalt: cannot step *)
      simpl in Hex. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Main results                                                        *)
(* ------------------------------------------------------------------ *)

Theorem program_typed_tyenv_preserves :
  forall P Θ,
    program_typed P Θ ->
    tyenv_preserves P (gamma_of P Θ).
Proof.
  intros P Θ HPT s s' Hwf Hstep.
  destruct Hwf as [Hg _].
  apply gamma_wf_state; [exact HPT |].
  eapply gamma_preserved; eauto.
Qed.

(* type_safety from Safety.v, instantiated at the concrete tyenv, with
   the tyenv_preserves obligation discharged.  No assumptions remain. *)
Theorem typed_type_safety :
  forall P Θ s,
    program_typed P Θ ->
    wf_state P (gamma_of P Θ) s ->
    (exists s', step P s s' /\ wf_state P (gamma_of P Θ) s') \/ terminal P s.
Proof.
  intros P Θ s HPT Hwf.
  apply type_safety.
  - apply program_typed_tyenv_preserves. exact HPT.
  - exact Hwf.
Qed.

(* Convenient entry point: a state at the start of a typed block whose
   registers satisfy the block's entry type is well-formed. *)
Theorem typed_start_wf :
  forall P Θ s l b,
    program_typed P Θ ->
    pcv s = pc_jump l ->
    P l = Some b ->
    mem_total (mm s) ->
    state_satisfies (Θ l) s ->
    wf_state P (gamma_of P Θ) s.
Proof.
  intros P Θ s l b HPT Hpc Hb Htot Hsat.
  apply gamma_wf_state; [exact HPT |].
  split; [exact Htot |].
  exists (Θ l). split.
  - exists b. rewrite Hpc. simpl. split; [exact Hb |]. split; [lia |].
    destruct (HPT l b Hb) as (R_end & Hchain & Htm).
    exists R_end. split; [exact Hchain | exact Htm].
  - exact Hsat.
Qed.
