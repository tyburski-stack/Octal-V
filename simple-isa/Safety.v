Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool Lists.List.
From SimpleIsa Require Import Syntax Machine.

(* Abstract typing layer / well-formedness predicates *)

(** replace terminal parameter with actual definition *)
Definition terminal (P : prog) (s : state) : Prop :=
  fetch P (pcv s) = Some (FTerm THalt).

(** define helper predicates for "safe to execute" *)
Definition instr_safe (s : state) (i : instr) : Prop :=
  exists s', exec_instr s i = Some s'.

Definition term_safe (s : state) (t : term) : Prop :=
  t = THalt \/ exists s', exec_term s t = Some s'.


(** make tyenv map PCs to precondition*)

Definition tyenv := pc -> state -> Prop.

(** definte wf state*)

Definition wf_state (P : prog) (Γ : tyenv) (s : state) : Prop :=
  Γ (pcv s) s /\
  match fetch P (pcv s) with
  | Some (FInstr i) => instr_safe s i
  | Some (FTerm t) => term_safe s t
  | None => False
  end.


(** add typing preservation condition for Γ *)
Definition tyenv_preserves (P : prog) (Γ : tyenv) : Prop :=
  forall s s',
    wf_state P Γ s ->
    step P s s' ->
    wf_state P Γ s'.

(* Determinism of the operational semantics *)
Lemma step_deterministic :
  forall (P : prog) (s s1 s2 : state),
    step P s s1 ->
    step P s s2 ->
    s1 = s2.
Proof.
  intros P s s1 s2 Hstep1 Hstep2.
  inversion Hstep1 as [s0 i s1' Hf1 He1 | s0 t s1' Hf1 He1]; subst.
  - inversion Hstep2 as [s0' i' s2' Hf2 He2 | s0' t' s2' Hf2 He2]; subst.
    + rewrite Hf1 in Hf2. inversion Hf2; subst.
      rewrite He1 in He2. inversion He2. reflexivity.
    + rewrite Hf1 in Hf2. discriminate.
  - inversion Hstep2 as [s0' i' s2' Hf2 He2 | s0' t' s2' Hf2 He2]; subst.
    + rewrite Hf1 in Hf2. discriminate.
    + rewrite Hf1 in Hf2. inversion Hf2; subst.
      rewrite He1 in He2. inversion He2. reflexivity.
Qed.

(* A well-typed state either has something fetchable at its pc,
   or is already terminal. *)
Lemma wf_state_fetch_or_terminal :
  forall (P : prog) (Γ : tyenv) (s : state),
    wf_state P Γ s ->
    (exists f, fetch P (pcv s) = Some f) \/ terminal P s.
Proof.
  intros P Γ s Hwf.
  unfold wf_state in Hwf.
  destruct Hwf as [_ Hsafe].
  destruct (fetch P (pcv s)) as [f |] eqn:Hfetch.
  - left. exists f. reflexivity.
  - contradiction.
Qed.

(* If a well-typed state fetches a normal instruction, then that
   instruction can execute safely. *)
Lemma wf_fetch_instr_safe :
  forall (P : prog) (Γ : tyenv) (s : state) (i : instr),
    wf_state P Γ s ->
    fetch P (pcv s) = Some (FInstr i) ->
    exists s', exec_instr s i = Some s'.
Proof.
  intros P Γ s i Hwf Hfetch.
  unfold wf_state in Hwf.
  destruct Hwf as [_ Hsafe].
  rewrite Hfetch in Hsafe.
  unfold instr_safe in Hsafe.
  exact Hsafe.
Qed.

(* If a well-typed state fetches a terminator, then it is either
   terminal or the terminator executes safely. *)
Lemma wf_fetch_term_safe :
  forall (P : prog) (Γ : tyenv) (s : state) (t : term),
    wf_state P Γ s ->
    fetch P (pcv s) = Some (FTerm t) ->
    terminal P s \/ exists s', exec_term s t = Some s'.
Proof.
  intros P Γ s t Hwf Hfetch.
  unfold wf_state in Hwf.
  destruct Hwf as [_ Hsafe].
  rewrite Hfetch in Hsafe.
  unfold term_safe in Hsafe.
  destruct Hsafe as [Ht | Hexec].
  - subst.
    left.
    unfold terminal.
    exact Hfetch.
  - right.
    exact Hexec.
Qed.

(* Progress: a well-typed state either terminates or can step. *)
Lemma progress :
  forall (P : prog) (Γ : tyenv) (s : state),
    wf_state P Γ s ->
    terminal P s \/ exists s', step P s s'.
Proof.
  intros P Γ s Hwf.
  unfold wf_state in Hwf.
  destruct Hwf as [_ Hsafe].
  destruct (fetch P (pcv s)) as [f |] eqn:Hfetch.
  - destruct f as [i | t].
    + unfold instr_safe in Hsafe.
      destruct Hsafe as [s' Hexec].
      right.
      exists s'.
      apply StepInstr with (i := i).
      * exact Hfetch.
      * exact Hexec.
    + unfold term_safe in Hsafe.
      destruct Hsafe as [Ht | [s' Hexec]].
      * subst.
        left.
        unfold terminal.
        exact Hfetch.
      * right.
        exists s'.
        apply StepTerm with (t := t).
        -- exact Hfetch.
        -- exact Hexec.
  - contradiction.
Qed.

(* Preservation: stepping preserves well-typedness. *)
Lemma preservation :
  forall (P : prog) (Γ : tyenv) (s s' : state),
    tyenv_preserves P Γ ->
    wf_state P Γ s ->
    step P s s' ->
    wf_state P Γ s'.
Proof.
  intros P Γ s s' Hpres Hwf Hstep.
  unfold tyenv_preserves in Hpres.
  eapply Hpres; eauto.
Qed.

(* Type safety (THEOREM 3): a well-typed state either terminates or steps to
   another well-typed state. *)
Theorem type_safety :
  forall (P : prog) (Γ : tyenv) (s : state),
    tyenv_preserves P Γ ->
    wf_state P Γ s ->
    (exists s', step P s s' /\ wf_state P Γ s') \/ terminal P s.
Proof.
  intros P Γ s Hpres Hwf.
  destruct (progress P Γ s Hwf) as [Hterm | [s' Hstep]].
  - right. exact Hterm.
  - left. exists s'. split.
    + exact Hstep.
    + eapply preservation; eauto.
Qed.