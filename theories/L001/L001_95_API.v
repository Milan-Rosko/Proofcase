(*L001_95_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / L001_95_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Public API surface for L001. This file exports the complete Aporetic
  closure layer, then names the package-level contract that the artifact
  boundary certifies. Downstream packages should import this file when they
  need the stable vocabulary and propositions, and `L001_97_Artifacts` when
  they need the certified contract endpoints and assumption reports.

  The API is intentionally expressed at the generic closure level first. The
  M001 regulator instance remains available through the exported lower files,
  but the mathematical core is the closure predicate `Formula -> Prop`,
  closure equivalence, evaluation closure, negation fixed points, collapse,
  and consistency obstruction.

*)

From L001 Require Export L001_02__Aporetic_Obstruction.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            PUBLIC CLOSURE ALIASES                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A closure theory is a formula-indexed predicate. This alias
│          is only a stable public spelling for the existing primitive
│          shape.
│
*)

Definition ClosureTheory : Type := Formula -> Prop.

(*
│
│          Stable public spelling for a closure-level negation fixed
│          point.
│
*)

Definition ClosureNegationFixedPoint
    (C : ClosureTheory)
    (B : Formula) : Prop :=
  NegationFixedPointFor C B.

(*
│
│          A closure decider is precisely a sound Boolean decision
│          record for the closure. The record contains the function
│          `Formula -> bool` and branch soundness proofs.
│
*)

Definition ClosureDecider
    (C : ClosureTheory) : Type :=
  ClosureDecision C.

(*
│
│          Propositional existential form of decider availability.
│          This is the shape used by the exported impossibility
│          statement: if such a function exists under the evaluation
│          and consistency hypotheses, the closure collapses by
│          reductio.
│
*)

Definition ClosureDeciderExists
    (C : ClosureTheory) : Prop :=
  exists D : ClosureDecider C,
    True.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               PUBLIC CONTRACT                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Evaluation closure supplies a formula equivalent, inside
│          the closure predicate, to its own object-level negation.
│
*)

Definition APORETIC_FIXED_POINT_CONTRACT : Prop :=
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    exists B : Formula,
      ClosureNegationFixedPoint C B.

(*
│
│          Evaluation closure plus closure-level excluded middle
│          collapses to bottom inside the same closure predicate.
│
*)

Definition APORETIC_EXCLUDED_MIDDLE_COLLAPSE_CONTRACT : Prop :=
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureModusPonens C ->
    ClosureExcludedMiddle C ->
    exists B : Formula,
      ClosureNegationFixedPoint C B /\
      (C B \/ C (formula_negation B)) /\
      C Bot.

(*
│
│          If the same closure is externally consistent, closure-level
│          excluded middle is impossible under evaluation closure.
│
*)

Definition APORETIC_EXCLUDED_MIDDLE_OBSTRUCTION_CONTRACT : Prop :=
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureExcludedMiddle C ->
    False.

(*
│
│          A sound Boolean decider is stronger than closure-level
│          excluded middle, so it also collapses the closure to bottom
│          under evaluation closure.
│
*)

Definition APORETIC_DECISION_COLLAPSE_CONTRACT : Prop :=
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureModusPonens C ->
    ClosureDecision C ->
    exists B : Formula,
      ClosureNegationFixedPoint C B /\
      (C B \/ C (formula_negation B)) /\
      C Bot.

(*
│
│          The decision-obstruction contract is the ad absurdum form:
│          under evaluation closure, modus-ponens closure, and
│          consistency, a sound total Boolean decider cannot exist.
│
*)

Definition APORETIC_DECISION_OBSTRUCTION_CONTRACT : Prop :=
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureDecision C ->
    False.

(*
│
│          Equivalence/ad-absurdum endpoint. Once a formula `B` is
│          equivalent inside the closure to `formula_negation B`, any
│          sound decision of that closure contradicts consistency.
│          This statement isolates the final reductio step from the
│          evaluation machinery that produces `B`.
│
*)

Definition APORETIC_EQUIVALENCE_AD_ABSURDUM_IMPOSSIBILITY_CONTRACT : Prop :=
  forall (C : ClosureTheory) (B : Formula),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureNegationFixedPoint C B ->
    ClosureDecision C ->
    False.

(*
│
│          Decider-existence endpoint. If some function decides the
│          closure by providing a sound Boolean decision record, then
│          no such function exists under the evaluation, modus-ponens
│          closure, and consistency hypotheses.
│
*)

Definition APORETIC_DECIDER_IMPOSSIBILITY_CONTRACT : Prop :=
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureDeciderExists C ->
    False.

(*
│
│          Complete package contract certified by `L001_97_Artifacts`.
│
*)

Definition APORETIC_LEMMA_CONTRACT : Prop :=
  APORETIC_FIXED_POINT_CONTRACT /\
  APORETIC_EXCLUDED_MIDDLE_COLLAPSE_CONTRACT /\
  APORETIC_EXCLUDED_MIDDLE_OBSTRUCTION_CONTRACT /\
  APORETIC_DECISION_COLLAPSE_CONTRACT /\
  APORETIC_DECISION_OBSTRUCTION_CONTRACT /\
  APORETIC_EQUIVALENCE_AD_ABSURDUM_IMPOSSIBILITY_CONTRACT /\
  APORETIC_DECIDER_IMPOSSIBILITY_CONTRACT.

Definition WITNESS : Prop :=
  APORETIC_LEMMA_CONTRACT.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            CONTRADICTION SURFACE                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Stable contradiction-shaped surface for the L001 reductio
│          endpoints. Each lemma is a one-line `exact` referring to
│          the underlying obstruction theorem in
│          `L001_02__Aporetic_Obstruction`; no new mathematics is
│          introduced. Names follow the pattern
│          `*_contradiction_from_*`.
│
*)

Theorem aporetic_contradiction_from_excluded_middle :
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureExcludedMiddle C ->
    False.
Proof.
  exact aporetic_obstruction.
Qed.

Theorem aporetic_contradiction_from_decision :
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureDecision C ->
    False.
Proof.
  intros C Code E Hcons Hmp D.
  exact
    (aporetic_contradiction_from_excluded_middle
       C Code E Hcons Hmp
       (decision_to_lem C D)).
Qed.

Theorem aporetic_contradiction_from_decider :
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureDeciderExists C ->
    False.
Proof.
  intros C Code E Hcons Hmp [D _].
  exact (aporetic_contradiction_from_decision C Code E Hcons Hmp D).
Qed.

Theorem aporetic_contradiction_from_neg_fixed_point :
  forall (C : ClosureTheory) (B : Formula),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureNegationFixedPoint C B ->
    ClosureDecision C ->
    False.
Proof.
  intros C B Hcons Hmp Hfix D.
  exact
    (negfixp_obstructs_lem
       C B Hcons Hmp Hfix
       (decision_to_lem C D)).
Qed.

Theorem regulator_contradiction_from_excluded_middle :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code),
    RegulatorClosureConsistent profile T Gamma ->
    RegulatorClosureExcludedMiddle profile T Gamma ->
    False.
Proof.
  exact regulator_aporetic_obstruction.
Qed.

Theorem regulator_contradiction_from_decision :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code),
    RegulatorClosureConsistent profile T Gamma ->
    RegulatorDecision profile T Gamma ->
    False.
Proof.
  exact regulator_decision_obstruction.
Qed.

Theorem regulator_contradiction_from_neg_fixed_point :
  forall profile T Gamma B,
    RegulatorClosureConsistent profile T Gamma ->
    RegulatorNegationFixedPoint profile T Gamma B ->
    RegulatorDecision profile T Gamma ->
    False.
Proof.
  exact negfixp_obstructs_regulator_decision.
Qed.

Theorem regulator_contradiction_from_aporetic_status_yes :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code)
         (excluded_middle_status : Formula),
    RegulatorClosureConsistent profile T Gamma ->
    YesBranchDecides profile T Gamma excluded_middle_status ->
    RegulatorClosure profile T Gamma excluded_middle_status ->
    False.
Proof.
  exact aporetic_status_yes_obstructed_lemma.
Qed.
