(*L001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / L001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  L001 uses M001 syntax and regulator adapters, but its generic `C : Formula
  -> Prop` has only the properties explicitly assumed by each theorem.

  The live source theorem uses the goal frame naming only `x ↦ ev x x → G`;
  the paper's stronger universal frame remains an adapter and corollary
  interface.

  `ClosureExcludedMiddle` and `ClosureDecision` classify acceptance of `A`
  versus `¬A`; the Boolean form carries internal evidence on either verdict.
  See the README for the undecidability and Lawvere/Curry reading.

*)

From M001 Require Export M001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   BOUNDARY                                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Goal evaluation yields `B ≃_C ¬B`; a local accepted branch
│          activates modus ponens, and consistency rejects the
│          resulting `C Bot`.
│
*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        CONSTRUCTIVE CLOSURE PREDICATE                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `ClosureEquiv C A B` consists exactly of the two accepted
│          implications `A → B` and `B → A`; further laws require
│          explicit premises.
│
*)

(*                       A ≃_C B ≔ C(A → B) ∧ C(B → A).                       *)

Definition ClosureEquiv
    (C : Formula -> Prop)
    (A B : Formula) : Prop :=
  C (Imp A B) /\ C (Imp B A).

(*
│
│          `closure_equiv_sym_lemma` records that closure equivalence
│          is symmetric by definition: the two accepted implication
│          directions are merely swapped.
│
*)

(*                             A ≃_C B ⇒ B ≃_C A.                             *)

Lemma closure_equiv_sym_lemma :
  forall (C : Formula -> Prop) A B,
    ClosureEquiv C A B ->
    ClosureEquiv C B A.
Proof.
  intros C A B [HAB HBA].
  split; assumption.
Qed.

(*
│
│          `ClosureExcludedMiddle C` supplies the Rocq-level branch `C
│          A \/ C (¬A)` for every formula; it is not an
│          object-language disjunction.
│
*)

(*               ClosureExcludedMiddle(C) ≔ ∀ A, C(A) ∨ C(¬A).                *)

Definition ClosureExcludedMiddle
    (C : Formula -> Prop) : Prop :=
  forall A : Formula,
    C A \/ C (formula_negation A).

(*
│
│          `ClosureModusPonens C` is top-level detachment only; it
│          neither introduces nor discharges assumptions.
│
*)

(*              ModusPonens(C) ≔ ∀ A B, C(A → B) ⇒ C(A) ⇒ C(B).               *)

Definition ClosureModusPonens
    (C : Formula -> Prop) : Prop :=
  forall A B,
    C (Imp A B) ->
    C A ->
    C B.

(*
│
│          `ClosureImplicationCongruence C` names left-congruence of
│          object-language implication under closure equivalence. If
│          `A` and `B` are equivalent in the closure, then
│          postcomposing both with the same goal `G` preserves
│          equivalence. This is not derivable from modus ponens alone;
│          when it is used below, it is an explicit load-bearing
│          hypothesis.
│
*)

(*                       A ≃_C B ⇒ (A → G) ≃_C (B → G).                       *)

Definition ClosureImplicationCongruence
    (C : Formula -> Prop) : Prop :=
  forall A B G,
    ClosureEquiv C A B ->
    ClosureEquiv C (Imp A G) (Imp B G).

(*
│
│          `closure_equiv_trans_lemma` derives transitivity of closure
│          equivalence from modus ponens plus implication congruence.
│          The forward direction chains through `(Y → Z) → (X → Z)`;
│          the backward direction uses symmetry first and then the
│          same left-congruence principle.
│
*)

(*         ModusPonens(C) ∧ ImpCong(C) ∧ X ≃_C Y ∧ Y ≃_C Z ⇒ X ≃_C Z.         *)

Lemma closure_equiv_trans_lemma :
  forall (C : Formula -> Prop),
    ClosureModusPonens C ->
    ClosureImplicationCongruence C ->
    forall X Y Z,
      ClosureEquiv C X Y ->
      ClosureEquiv C Y Z ->
      ClosureEquiv C X Z.
Proof.
  intros C Hmodus_ponens Hcongruence X Y Z HXY HYZ.
  split.
  - destruct (Hcongruence X Y Z HXY) as [_ H_YZ_to_XZ].
    exact
      (Hmodus_ponens
         (Imp Y Z) (Imp X Z)
         H_YZ_to_XZ
         (proj1 HYZ)).
  - destruct
      (Hcongruence Z Y X (closure_equiv_sym_lemma C Y Z HYZ))
      as [_ H_YX_to_ZX].
    exact
      (Hmodus_ponens
         (Imp Y X) (Imp Z X)
         H_YX_to_ZX
         (proj2 HXY)).
Qed.

(*
│
│          `ClosureConsistent C` is the external consistency guard for
│          a closure predicate: acceptance of the object-level bottom
│          formula makes the ambient Rocq context contradictory. It
│          turns an already constructed `C Bot` into an obstruction.
│
*)

(*                       Consistent(C) ≔ C(⊥) → False.                        *)

Definition ClosureConsistent
    (C : Formula -> Prop) : Prop :=
  C Bot -> False.

(*
│
│          `NegationFixedPointFor C B` says that `B` is a negation
│          fixed point inside the closure predicate: `B` and its
│          object-level negation imply each other under `C`. Collapse
│          requires an additional accepted branch.
│
*)

(*                   NegationFixedPointFor(C,B) ≔ B ≃_C ¬B.                   *)

Definition NegationFixedPointFor
    (C : Formula -> Prop)
    (B : Formula) : Prop :=
  ClosureEquiv C B (formula_negation B).

(*
│
│          `ClosureLocalExcludedMiddle C B` is the single internal
│          bivalence commitment at the formula `B`: either `C B` or `C
│          (¬B)`. It is the local branch datum used by the core
│          obstruction and is strictly weaker in shape than global
│          `ClosureExcludedMiddle C`.
│
*)

(*                       LocalLEM(C,B) ≔ C(B) ∨ C(¬B).                        *)

Definition ClosureLocalExcludedMiddle
    (C : Formula -> Prop)
    (B : Formula) : Prop :=
  C B \/ C (formula_negation B).

(*
│
│          Global closure excluded middle immediately supplies the
│          local branch datum at any chosen formula.
│
*)

(*                 ClosureExcludedMiddle(C) ⇒ LocalLEM(C,B).                  *)

Theorem closure_lem_to_local_lemma :
  forall (C : Formula -> Prop) (B : Formula),
    ClosureExcludedMiddle C ->
    ClosureLocalExcludedMiddle C B.
Proof.
  intros C B Hlem.
  exact (Hlem B).
Qed.

(*
│
│          `ClosureDecision C` gives a Boolean verdict certified by `C
│          A` or `C (¬A)`. Under consistency and modus ponens the
│          negative certificate entails `~ C A`, while retaining the
│          internal branch evidence used by the collapse.
│
*)

(*                           decide(A)=true ⇒ C(A)                            *)
(*                          decide(A)=false ⇒ C(¬A).                          *)

Record ClosureDecision
    (C : Formula -> Prop)
    : Type := {
  cdecide : Formula -> bool;

  cdecide_true_sound :
    forall A,
      cdecide A = true ->
      C A;

  cdecide_false_sound :
    forall A,
      cdecide A = false ->
      C (formula_negation A)
}.

Arguments cdecide {C} _ _.
Arguments cdecide_true_sound {C} _ _ _.
Arguments cdecide_false_sound {C} _ _ _.

(*
│
│          `decision_to_lem` is the adapter from a Boolean status
│          classifier to closure-level excluded middle. It is a
│          transport lemma: later decision-collapse results use this
│          route before applying the generic excluded-middle collapse
│          theorem.
│
*)

(*               ClosureDecision(C) ⇒ ClosureExcludedMiddle(C).               *)

Theorem decision_to_lem :
  forall C,
    ClosureDecision C ->
    ClosureExcludedMiddle C.
Proof.
  intros C D A.
  destruct (cdecide D A) eqn:Hdec.
  - left.
    apply (cdecide_true_sound D A).
    exact Hdec.
  - right.
    apply (cdecide_false_sound D A).
    exact Hdec.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         GENERIC CLOSURE FIXED POINT                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The live construction uses the goal-specific frame; the
│          universal frame remains the paper-facing interface and
│          supplies it by an adapter.
│
*)

(*
│
│          `ClosureEvaluationFrame` names every formula-valued coded
│          behavior up to `ClosureEquiv`.
│
*)

(*         EvalComplete(C,Code) ≔ ∀ f, ∃ c, ∀ x, eval(c,x) ≃_C f(x).          *)

Record ClosureEvaluationFrame
    (C : Formula -> Prop)
    (Code : Type) : Type := {
  ceval_apply : Code -> Code -> Formula;

  cevaluation_complete :
    forall f : Code -> Formula,
      exists c : Code,
        forall x : Code,
          ClosureEquiv C
            (ceval_apply c x)
            (f x)
}.

Arguments ceval_apply {C Code} _ _ _.
Arguments cevaluation_complete {C Code} _ _.

(*
│
│          `ClosureEvaluationFrameForGoal` names only `x ↦ ev x x →
│          G`, the behavior used by the live diagonal theorem.
│
*)

(*             EvC_G(C,ev,G) ≔ ∃c. ∀x, ev(c,x) ≃_C (ev(x,x) → G).             *)

Definition ClosureEvaluationFrameForGoal
    (C : Formula -> Prop)
    (Code : Type)
    (ev : Code -> Code -> Formula)
    (G : Formula) : Prop :=
  exists c : Code,
    forall x : Code,
      ClosureEquiv C
        (ev c x)
        (Imp (ev x x) G).

(*
│
│          A full closure evaluation frame supplies the goal-specific
│          fragment for every goal `G` by applying universal
│          completeness to the behavior `x ↦ ev(x,x) → G`.
│
*)

(*                    EvalComplete(C,ev) ⇒ EvC_G(C,ev,G).                     *)

Lemma closure_evaluation_frame_implies_goal_frame_lemma :
  forall (C : Formula -> Prop) Code
         (E : ClosureEvaluationFrame C Code)
         (G : Formula),
    ClosureEvaluationFrameForGoal C Code (ceval_apply E) G.
Proof.
  intros C Code E G.
  exact
    (cevaluation_complete E
       (fun x => Imp (ceval_apply E x x) G)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           GOAL-FRAME DECOMPOSITION                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `ClosureDiagonalRep` says that self-application itself is
│          representable: one code `d` names the behavior `x ↦
│          ev(x,x)` up to closure equivalence.
│
*)

(*                DiagRep(C,ev) ≔ ∃d. ∀x, ev(d,x) ≃_C ev(x,x).                *)

Definition ClosureDiagonalRep
    (C : Formula -> Prop)
    (Code : Type)
    (ev : Code -> Code -> Formula) : Prop :=
  exists d : Code,
    forall x : Code,
      ClosureEquiv C (ev d x) (ev x x).

(*
│
│          `ClosureGoalImpRep C Code ev G` says that any representable
│          behavior can be postcomposed with implication into the
│          fixed goal `G`. This names the representation step
│          separately from implication congruence.
│
*)

(*       GoalImpRep(C,ev,G) ≔ ∀e. ∃e'. ∀x, ev(e',x) ≃_C (ev(e,x) → G).        *)

Definition ClosureGoalImpRep
    (C : Formula -> Prop)
    (Code : Type)
    (ev : Code -> Code -> Formula)
    (G : Formula) : Prop :=
  forall e : Code,
    exists e' : Code,
      forall x : Code,
        ClosureEquiv C
          (ev e' x)
          (Imp (ev e x) G).

(*
│
│          The decomposition theorem states that diagonal
│          representability plus goal-implication representability
│          yields the goal frame, provided the closure can transport
│          equivalence through implication and compose equivalences.
│          The composition step is exactly where `ClosureModusPonens`
│          and `ClosureImplicationCongruence` are used.
│
*)

(*     ModusPonens(C) ∧ ImpCong(C) ∧ DiagRep(C,ev) ∧ GoalImpRep(C,ev,G) ⇒     *)
(*                               EvC_G(C,ev,G).                               *)

Theorem closure_diagonal_plus_imp_rep_yields_goal_frame_lemma :
  forall (C : Formula -> Prop) Code
         (ev : Code -> Code -> Formula)
         (G : Formula),
    ClosureModusPonens C ->
    ClosureImplicationCongruence C ->
    ClosureDiagonalRep C Code ev ->
    ClosureGoalImpRep C Code ev G ->
    ClosureEvaluationFrameForGoal C Code ev G.
Proof.
  intros C Code ev G Hmodus_ponens Hcongruence [d Hdiagonal] Hgoal_imp.
  destruct (Hgoal_imp d) as [d' Hd'].
  exists d'.
  intro x.
  apply
    (closure_equiv_trans_lemma
       C Hmodus_ponens Hcongruence
       (ev d' x)
       (Imp (ev d x) G)
       (Imp (ev x x) G)).
  - exact (Hd' x).
  - exact (Hcongruence (ev d x) (ev x x) G (Hdiagonal x)).
Qed.

(*
│
│          `generic_fixp_existence` is the generic fixed-point
│          adapter. If the evaluation frame can name every coded
│          behavior up to `ClosureEquiv`, then every formula
│          transformer `g` has a closure-level fixed point.
│
*)

(*                  EvalComplete(C) ⇒ ∀ g, ∃ B, B ≃_C g(B).                   *)

Theorem generic_fixp_existence :
  forall (C : Formula -> Prop) Code
         (E : ClosureEvaluationFrame C Code)
         (g : Formula -> Formula),
    exists B : Formula,
      ClosureEquiv C B (g B).
Proof.
  intros C Code E g.
  destruct
    (cevaluation_complete E
      (fun x => g (ceval_apply E x x)))
    as [c Hc].
  exists (ceval_apply E c c).
  apply Hc.
Qed.

(*
│
│          `negfixp_existence` is the generic diagonal step.
│          Evaluation completeness names the behavior `x ↦ ¬ eval(x,
│          x)`; running that name on itself yields a formula
│          equivalent, under `C`, to its own object-level negation.
│
*)

(*                  evaluation-complete(C) ⇒ ∃ B, B ≃_C ¬B.                   *)

Theorem negfixp_existence :
  forall (C : Formula -> Prop) Code
         (E : ClosureEvaluationFrame C Code),
    exists B : Formula,
      NegationFixedPointFor C B.
Proof.
  intros C Code E.
  destruct
    (generic_fixp_existence C Code E formula_negation)
    as [B Hfix].
  exists B.
  exact Hfix.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           M001 REGULATOR INSTANCE                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `RegulatorClosure profile T Gamma` is the L001 spelling of
│          the M001 closure predicate generated from an axiom set. It
│          keeps the fixed-point theorem at the closure-predicate
│          level while making the concrete regulator instance
│          explicit.
│
*)

(*                     RegulatorClosure(profile,T,Γ,A) ≔                      *)
(* regulator_theory_closure(regulator_theory_with_axiom_set(profile,T),Γ,A).  *)

Definition RegulatorClosure
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    (A : Formula) : Prop :=
  regulator_theory_closure
    (regulator_theory_with_axiom_set profile T)
    Gamma A.

(*
│
│          `RegulatorClosureEvaluationFrame` is an M001 evaluation
│          frame over the regulator theory induced by `profile` and
│          `T`. L001 uses this alias to avoid hiding the axiom-set
│          origin of the closure predicate.
│
*)

(*            RegulatorClosureEvaluationFrame(profile,T,Γ,Code) ≔             *)
(*RegulatorEvaluationFrame(regulator_theory_with_axiom_set(profile,T),Γ,Code).*)

Definition RegulatorClosureEvaluationFrame
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    (Code : Type) : Type :=
  RegulatorEvaluationFrame
    (regulator_theory_with_axiom_set profile T)
    Gamma Code.

(*
│
│          `regulator_closure_evaluation_frame` reads an M001
│          regulated evaluation frame as a generic closure evaluation
│          frame. This adapter is presentation-only: the closure
│          predicate remains `RegulatorClosure profile T Gamma`, the
│          M001 regulator-theory predicate.
│
*)

(*             EvalComplete(RegulatorClosure(profile,T,Γ),Code).              *)

Definition regulator_closure_evaluation_frame
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    (Code : Type)
    (E : RegulatorClosureEvaluationFrame profile T Gamma Code)
    : ClosureEvaluationFrame (RegulatorClosure profile T Gamma) Code :=
  {|
    ceval_apply := regulator_evaluation_apply E;
    cevaluation_complete := regulator_evaluation_complete E
  |}.

(*
│
│          `regulator_closure_modus_ponens_lemma` specializes the
│          generic `ClosureModusPonens` contract to the M001 regulator
│          predicate for use in the later collapse proofs.
│
*)

(*                ModusPonens(RegulatorClosure(profile,T,Γ)).                 *)

Theorem regulator_closure_modus_ponens_lemma :
  forall profile T Gamma,
    ClosureModusPonens (RegulatorClosure profile T Gamma).
Proof.
  intros profile T Gamma A B Himp HA.
  exact
    (regulator_theory_closure_closed_under_mp_lemma
       (regulator_theory_with_axiom_set profile T)
       Gamma A B Himp HA).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       REGULATOR-LEVEL EXCLUDED MIDDLE                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `RegulatorClosureExcludedMiddle` specializes object-level
│          `ClosureExcludedMiddle` to `RegulatorClosure profile T
│          Gamma`: every formula or its object-level negation is
│          accepted by the regulator predicate.
│
*)

(*             RegulatorClosureExcludedMiddle(profile,T,Γ) ≔ ∀ A,             *)
(*    RegulatorClosure(profile,T,Γ,A) ∨ RegulatorClosure(profile,T,Γ,¬A).     *)

Definition RegulatorClosureExcludedMiddle
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context) : Prop :=
  forall A : Formula,
    RegulatorClosure profile T Gamma A \/
    RegulatorClosure profile T Gamma (formula_negation A).

(*
│
│          `RegulatorDecision` specializes the internally witnessed
│          Boolean decision to `RegulatorClosure`.
│
*)

(*             rdecide(A)=true ⇒ RegulatorClosure(profile,T,Γ,A)              *)
(*            rdecide(A)=false ⇒ RegulatorClosure(profile,T,Γ,¬A).            *)

Record RegulatorDecision
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    : Type := {
  rdecide : Formula -> bool;

  rdecide_true_sound :
    forall A,
      rdecide A = true ->
      RegulatorClosure profile T Gamma A;

  rdecide_false_sound :
    forall A,
      rdecide A = false ->
      RegulatorClosure profile T Gamma (formula_negation A)
}.

Arguments rdecide {profile T Gamma} _ _.
Arguments rdecide_true_sound {profile T Gamma} _ _ _.
Arguments rdecide_false_sound {profile T Gamma} _ _ _.

(*
│
│          `regulator_decision_to_lem` is the M001 instance of the
│          decision-to-excluded-middle adapter: a total regulator
│          classifier yields regulator-level excluded middle by
│          splitting on the Boolean status and applying the soundness
│          certificate for the selected branch.
│
*)

(*                      RegulatorDecision(profile,T,Γ) ⇒                      *)
(*                RegulatorClosureExcludedMiddle(profile,T,Γ).                *)

Theorem regulator_decision_to_lem :
  forall profile T Gamma,
    RegulatorDecision profile T Gamma ->
    RegulatorClosureExcludedMiddle profile T Gamma.
Proof.
  intros profile T Gamma D A.
  destruct (rdecide D A) eqn:Hdec.
  - left.
    apply (rdecide_true_sound D A).
    exact Hdec.
  - right.
    apply (rdecide_false_sound D A).
    exact Hdec.
Qed.

(*
│
│          `regulator_lem_iff_closure_lem` identifies regulator-level
│          excluded middle with the generic closure-level
│          excluded-middle contract for the M001 closure predicate. It
│          is an adapter lemma, so later regulator consequences can
│          reuse the generic closure theorems without restating their
│          proofs.
│
*)

(*               RegulatorClosureExcludedMiddle(profile,T,Γ) ↔                *)
(*           ClosureExcludedMiddle(RegulatorClosure(profile,T,Γ)).            *)

Theorem regulator_lem_iff_closure_lem :
  forall profile T Gamma,
    RegulatorClosureExcludedMiddle profile T Gamma <->
    ClosureExcludedMiddle (RegulatorClosure profile T Gamma).
Proof.
  intros profile T Gamma.
  unfold RegulatorClosureExcludedMiddle, ClosureExcludedMiddle.
  split; intro H; exact H.
Qed.

(*
│
│          `regulator_decision_as_closure_decision` reads an M001
│          regulator classifier as a generic closure decision. The
│          Boolean function and its branch soundness certificates are
│          unchanged; only the surrounding contract vocabulary is
│          generalized.
│
*)

(*                      RegulatorDecision(profile,T,Γ) ⇒                      *)
(*              ClosureDecision(RegulatorClosure(profile,T,Γ)).               *)

Definition regulator_decision_as_closure_decision
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    (D : RegulatorDecision profile T Gamma)
    : ClosureDecision (RegulatorClosure profile T Gamma) :=
  {|
    cdecide := rdecide D;
    cdecide_true_sound := rdecide_true_sound D;
    cdecide_false_sound := rdecide_false_sound D
  |}.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            STATUS BRANCH READINGS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `YesBranchDecides` converts acceptance of the status
│          formula into a total regulator decision.
│
*)

(*           RegulatorClosure(profile,T,Γ,excluded_middle_status) ⇒           *)
(*                      RegulatorDecision(profile,T,Γ).                       *)

Definition YesBranchDecides
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    (excluded_middle_status : Formula) : Type :=
  RegulatorClosure profile T Gamma excluded_middle_status ->
  RegulatorDecision profile T Gamma.

(*
│
│          `RegulatorRefutation` certifies negation only on true
│          results and is therefore weaker than `RegulatorDecision`.
│
*)

(*            rrefute(A)=true ⇒ RegulatorClosure(profile,T,Γ,¬A).             *)

Record RegulatorRefutation
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    : Type := {
  rrefute : Formula -> bool;

  rrefute_true_sound :
    forall A,
      rrefute A = true ->
      RegulatorClosure profile T Gamma (formula_negation A)
}.

Arguments rrefute {profile T Gamma} _ _.
Arguments rrefute_true_sound {profile T Gamma} _ _ _.

(*
│
│          `RegulatorDoubleNegationBridge` is an optional
│          regulator-context principle that converts accepted double
│          negations into accepted formulas. The no-branch obstruction
│          theorems in `L001_02` take it as an explicit local
│          hypothesis.
│
*)

(*double-negation bridge(profile,T,Γ) ≔ ∀ A, RegulatorClosure(profile,T,Γ,¬¬A)*)
(*                     ⇒ RegulatorClosure(profile,T,Γ,A).                     *)

Definition RegulatorDoubleNegationBridge
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context) : Prop :=
  forall A,
    RegulatorClosure profile T Gamma (formula_negation (formula_negation A)) ->
    RegulatorClosure profile T Gamma A.
