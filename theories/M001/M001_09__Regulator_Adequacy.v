(*M001_09__Regulator_Adequacy.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                   Proofcase / M001_09__Regulator_Adequacy                    │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Checker/regulator interface for regulator theories. The symbolic-regulator
  layer packages `regulator_theory_check_bool` as an abstract Boolean
  regulator. This file adds transparent machine names, formula-predicate
  closure views, and closure lemmas that restate the checked infrastructure
  in regulator-facing vocabulary.

  Everything in this layer is definitional or structural. The machine views
  are just checker functions, the closure views are just checked derivability
  predicates, and the symbolic-regulator equivalences are the existential
  wrapper identities from `M001_08__Symbolic_Regulator`. No semantic
  validity, external model theory, modal provability, arithmetic coding,
  diagonal obstruction, or self-recognition principle is introduced here.

*)

From M001 Require Export M001_08__Symbolic_Regulator.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         MACHINE / CHECKER INTERFACE                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  `regulator_theory_machine R Γ` is the machine view of the regulator-theory
  checker: a Boolean function from proof scripts and requested output
  formulas to acceptance. It is definitionally `regulator_theory_check_bool R
  Γ`. The finite axiom-set machine is the same presentation for the
  finite-data checker.

(*  regulator_theory_machine(R,Γ,p,A) ≔ regulator_theory_check_bool(R,Γ,p,A)  *)
(*                finite_axiom_set_machine(profile,FT,Γ,p,A) ≔                *)
(*               finite_axiom_set_check_bool(profile,FT,Γ,p,A)                *)

Definition regulator_theory_machine
    (R : RegulatorTheory)
    (Gamma : Context)
    : Proof -> Formula -> bool :=
  fun p A => regulator_theory_check_bool R Gamma p A.

Definition finite_axiom_set_machine
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    : Proof -> Formula -> bool :=
  fun p A => finite_axiom_set_check_bool profile T Gamma p A.

Lemma regulator_theory_machine_runs_checker_lemma :
  forall R Gamma p A,
    regulator_theory_machine R Gamma p A =
    regulator_theory_check_bool R Gamma p A.
Proof.
  reflexivity.
Qed.

Lemma finite_axiom_set_machine_runs_checker_lemma :
  forall profile T Gamma p A,
    finite_axiom_set_machine profile T Gamma p A =
    finite_axiom_set_check_bool profile T Gamma p A.
Proof.
  reflexivity.
Qed.

  Machine acceptance and symbolic-regulator acceptance are the same Boolean
  event. These lemmas are useful when later layers want to speak in terms of
  an abstract `SymbolicRegulator` while still reducing acceptance back to the
  concrete checker.

(*                  regulator_theory_machine(R,Γ,p,A)=true ⇔                  *)
(*symbolic_regulator_accepts_bool(regulator_theory_symbolic_regulator(R,Γ),p,A)=true*)
(*             finite_axiom_set_machine(profile,FT,Γ,p,A)=true ⇔              *)
(*symbolic_regulator_accepts_bool(finite_axiom_set_symbolic_regulator(profile,FT,Γ),p,A)=true*)

Lemma regulator_theory_machine_acceptance_iff_symbolic_regulator_lemma :
  forall R Gamma p A,
    regulator_theory_machine R Gamma p A = true
    <->
    symbolic_regulator_accepts_bool
      (regulator_theory_symbolic_regulator R Gamma)
      p A = true.
Proof.
  intros R Gamma p A.
  unfold regulator_theory_machine,
    regulator_theory_symbolic_regulator,
    regulator_theory_regulates_bool.
  simpl.
  split; intro H; exact H.
Qed.

Lemma finite_axiom_set_machine_acceptance_iff_symbolic_regulator_lemma :
  forall profile T Gamma p A,
    finite_axiom_set_machine profile T Gamma p A = true
    <->
    symbolic_regulator_accepts_bool
      (finite_axiom_set_symbolic_regulator profile T Gamma)
      p A = true.
Proof.
  intros profile T Gamma p A.
  unfold finite_axiom_set_machine,
    finite_axiom_set_symbolic_regulator,
    finite_axiom_set_regulates_bool.
  simpl.
  split; intro H; exact H.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           REGULATOR-THEORY CLOSURE                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  `regulator_theory_closure R Γ` is the output-side predicate induced by the
  checker: a formula belongs to the closure exactly when it is
  checked-derivable from `Γ` under regulator theory `R`. The finite axiom-set
  closure is the finite-data counterpart.

(*                       closure_R,Γ(A) ≔ R; Γ ⊢check A                       *)
(*             closure_profile,FT,Γ(A) ≔ profile, FT; Γ ⊢check A              *)

Definition regulator_theory_closure
    (R : RegulatorTheory)
    (Gamma : Context)
    : Formula -> Prop :=
  fun A => regulator_theory_checked_derivable R Gamma A.

Definition finite_axiom_set_closure
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    : Formula -> Prop :=
  fun A => finite_axiom_set_checked_derivable profile T Gamma A.

Definition regulator_theory_equivalent
    (R : RegulatorTheory)
    (Gamma : Context)
    (A B : Formula) : Prop :=
  regulator_theory_closure R Gamma (Imp A B) /\
  regulator_theory_closure R Gamma (Imp B A).

(*           A ≃_{R,Γ} B ≔ closure_R,Γ(A → B) ∧ closure_R,Γ(B → A)            *)

Lemma regulator_theory_closure_iff_checked_derivable_lemma :
  forall R Gamma A,
    regulator_theory_closure R Gamma A <->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A.
  unfold regulator_theory_closure.
  split; intro H; exact H.
Qed.

Lemma finite_axiom_set_closure_iff_checked_derivable_lemma :
  forall profile T Gamma A,
    finite_axiom_set_closure profile T Gamma A <->
    finite_axiom_set_checked_derivable profile T Gamma A.
Proof.
  intros profile T Gamma A.
  unfold finite_axiom_set_closure.
  split; intro H; exact H.
Qed.

(*                              closure_R,Γ(A) ⇔                              *)
(*  symbolic_regulator_derivable(regulator_theory_symbolic_regulator(R,Γ),A)  *)

Lemma regulator_theory_closure_iff_symbolic_derivable_lemma :
  forall R Gamma A,
    regulator_theory_closure R Gamma A
    <->
    symbolic_regulator_derivable
      (regulator_theory_symbolic_regulator R Gamma)
      A.
Proof.
  intros R Gamma A.
  unfold regulator_theory_closure.
  symmetry.
  apply regulator_theory_symbolic_derivable_iff_checked_derivable_lemma.
Qed.

(*                         closure_profile,FT,Γ(A) ⇔                          *)
(*symbolic_regulator_derivable(finite_axiom_set_symbolic_regulator(profile,FT,Γ),A)*)

Lemma finite_axiom_set_closure_iff_symbolic_derivable_lemma :
  forall profile T Gamma A,
    finite_axiom_set_closure profile T Gamma A
    <->
    symbolic_regulator_derivable
      (finite_axiom_set_symbolic_regulator profile T Gamma)
      A.
Proof.
  intros profile T Gamma A.
  unfold finite_axiom_set_closure.
  symmetry.
  apply finite_axiom_set_symbolic_derivable_iff_checked_derivable_lemma.
Qed.

(*                         closure_profile,FT,Γ(A) ⇔                          *)
(*regulator_theory_closure(finite_axiom_set_to_regulator_theory(profile,FT),Γ,A)*)

Lemma finite_axiom_set_closure_as_regulator_theory_closure_lemma :
  forall profile T Gamma A,
    finite_axiom_set_closure profile T Gamma A
    <->
    regulator_theory_closure
      (finite_axiom_set_to_regulator_theory profile T)
      Gamma A.
Proof.
  intros profile T Gamma A.
  unfold finite_axiom_set_closure, regulator_theory_closure.
  apply finite_axiom_set_checked_derivable_as_regulator_theory_lemma.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CLOSURE PRINCIPLES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The closure lemmas restate the core checked principles under the
  formula-predicate view. MP preserves closure, deduction moves one context
  assumption into an implication, reductio yields object-language negation,
  and negative precomposition transports non-closure backward through a
  closed implication.

(*             closure_R,Γ(A→B) ∧ closure_R,Γ(A) ⇒ closure_R,Γ(B)             *)

Lemma regulator_theory_closure_closed_under_mp_lemma :
  forall R Gamma A B,
    regulator_theory_closure R Gamma (Imp A B) ->
    regulator_theory_closure R Gamma A ->
    regulator_theory_closure R Gamma B.
Proof.
  intros R Gamma A B Himp Harg.
  unfold regulator_theory_closure in *.
  apply regulator_theory_checked_derivable_mp_lemma
    with (A := A);
    assumption.
Qed.

(*                    closure_R,A::Γ(B) ⇒ closure_R,Γ(A→B)                    *)

Lemma regulator_theory_closure_deduction_lemma :
  forall R Gamma A B,
    regulator_theory_closure R (ctx_extend A Gamma) B ->
    regulator_theory_closure R Gamma (Imp A B).
Proof.
  intros R Gamma A B H.
  unfold regulator_theory_closure in *.
  apply regulator_theory_checked_derivable_deduction_lemma.
  exact H.
Qed.

(*                    closure_R,A::Γ(⊥) ⇒ closure_R,Γ(¬A)                     *)

Lemma regulator_theory_closure_reductio_lemma :
  forall R Gamma A,
    regulator_theory_closure R (ctx_extend A Gamma) Bot ->
    regulator_theory_closure R Gamma (formula_negation A).
Proof.
  intros R Gamma A H.
  unfold regulator_theory_closure in *.
  apply regulator_theory_checked_derivable_reductio_lemma.
  exact H.
Qed.

(*            closure_R,Γ(A→B) ∧ ¬closure_R,Γ(B) ⇒ ¬closure_R,Γ(A)            *)

Lemma regulator_theory_closure_negative_precomposition_lemma :
  forall R Gamma A B,
    regulator_theory_closure R Gamma (Imp A B) ->
    (regulator_theory_closure R Gamma B -> False) ->
    regulator_theory_closure R Gamma A -> False.
Proof.
  intros R Gamma A B Himp HnotB.
  unfold regulator_theory_closure in *.
  apply regulator_theory_not_checked_derivable_precompose_lemma
    with (B := B);
    [ exact Himp | exact HnotB ].
Qed.

(*                 Γ ≤ctx Δ ∧ closure_R,Γ(A) ⇒ closure_R,Δ(A)                 *)

Lemma regulator_theory_closure_context_monotone_lemma :
  forall R Gamma Delta A,
    context_included Gamma Delta ->
    regulator_theory_closure R Gamma A ->
    regulator_theory_closure R Delta A.
Proof.
  intros R Gamma Delta A Hinc H.
  unfold regulator_theory_closure in *.
  apply regulator_theory_checked_derivable_context_monotone_lemma
    with (Gamma := Gamma);
    assumption.
Qed.

(*                 R ≤rt S ∧ closure_R,Γ(A) ⇒ closure_S,Γ(A)                  *)

Lemma regulator_theory_closure_regulator_theory_monotone_lemma :
  forall R S Gamma A,
    regulator_theory_included R S ->
    regulator_theory_closure R Gamma A ->
    regulator_theory_closure S Gamma A.
Proof.
  intros R S Gamma A Hinc H.
  unfold regulator_theory_closure in *.
  apply regulator_theory_checked_derivable_regulator_theory_monotone_lemma
    with (R := R);
    assumption.
Qed.
