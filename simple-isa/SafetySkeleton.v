Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool Lists.List.
From SimpleIsa Require Import Syntax Machine.

(* Abstract typing layer / well-formedness predicates *)
Parameter tyenv : Type.

Parameter wf_state : prog -> tyenv -> state -> Prop.
Parameter terminal : prog -> state -> Prop.

(* Determinism of the operational semantics *)
Lemma step_deterministic :
  forall (P : prog) (s s1 s2 : state),
    step P s s1 ->
    step P s s2 ->
    s1 = s2.
Admitted.

(* A well-typed state either has something fetchable at its pc,
   or is already terminal. *)
Lemma wf_state_fetch_or_terminal :
  forall (P : prog) (Γ : tyenv) (s : state),
    wf_state P Γ s ->
    (exists f, fetch P (pcv s) = Some f) \/ terminal P s.
Admitted.

(* If a well-typed state fetches a normal instruction, then that
   instruction can execute safely. *)
Lemma wf_fetch_instr_safe :
  forall (P : prog) (Γ : tyenv) (s : state) (i : instr),
    wf_state P Γ s ->
    fetch P (pcv s) = Some (FInstr i) ->
    exists s', exec_instr s i = Some s'.
Admitted.

(* If a well-typed state fetches a terminator, then it is either
   terminal or the terminator executes safely. *)
Lemma wf_fetch_term_safe :
  forall (P : prog) (Γ : tyenv) (s : state) (t : term),
    wf_state P Γ s ->
    fetch P (pcv s) = Some (FTerm t) ->
    terminal P s \/ exists s', exec_term s t = Some s'.
Admitted.

(* Progress: a well-typed state either terminates or can step. *)
Lemma progress :
  forall (P : prog) (Γ : tyenv) (s : state),
    wf_state P Γ s ->
    terminal P s \/ exists s', step P s s'.
Admitted.

(* Preservation: stepping preserves well-typedness. *)
Lemma preservation :
  forall (P : prog) (Γ : tyenv) (s s' : state),
    wf_state P Γ s ->
    step P s s' ->
    wf_state P Γ s'.
Admitted.

(* Type safety (THEOREM 3): a well-typed state either terminates or steps to
   another well-typed state. *)
Theorem type_safety :
  forall (P : prog) (Γ : tyenv) (s : state),
    wf_state P Γ s ->
    (exists s', step P s s' /\ wf_state P Γ s') \/ terminal P s.
Admitted.