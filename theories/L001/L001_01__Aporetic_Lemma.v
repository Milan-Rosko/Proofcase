(*L001_01__Aporetic_Lemma.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / L001_01__Aporetic_Lemma                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Fixed-point and collapse layer. A goal frame produces `B ≃_C (B → G)`;
  primitive closure needs an accepted branch to derive `C G`.

  L002 obtains unconditional Curry collapse only after specializing to M001's
  richer assumption and deduction structure.

*)

From L001 Require Export L001_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          GENERIC CURRY FIXED POINT                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `CurryFixedPointFor C G B` abbreviates `B ≃_C (B → G)`; `G
│          := Bot` gives the negation fixed point.
│
*)

(*                 CurryFixedPointFor(C,G,B) ≔ B ≃_C (B → G).                 *)

Definition CurryFixedPointFor
    (C : Formula -> Prop)
    (G B : Formula) : Prop :=
  ClosureEquiv C B (Imp B G).

(*
│
│          Self-applying the code supplied by `EvC_G` produces `B ≃_C
│          (B → G)`.
│
*)

(*                     EvC_G(C,ev,G) ⇒ ∃B. B ≃_C (B → G).                     *)

Theorem curry_fixp_existence :
  forall (C : Formula -> Prop) Code
         (ev : Code -> Code -> Formula)
         (G : Formula),
    ClosureEvaluationFrameForGoal C Code ev G ->
    exists B : Formula,
      CurryFixedPointFor C G B.
Proof.
  intros C Code ev G [c Hc].
  exists (ev c c).
  exact (Hc c).
Qed.

(*
│
│          The full-frame corollary recovers the earlier universal
│          form: a `ClosureEvaluationFrame` implies `EvC_G` for each
│          goal, and therefore yields the Curry fixed point at that
│          goal.
│
*)

(*                EvalComplete(C,ev) ⇒ ∀G. ∃B. B ≃_C (B → G).                 *)

Theorem closure_evaluation_full_frame_curry_fixed_point_lemma :
  forall (C : Formula -> Prop) Code
         (E : ClosureEvaluationFrame C Code)
         (G : Formula),
    exists B : Formula,
      CurryFixedPointFor C G B.
Proof.
  intros C Code E G.
  exact
    (curry_fixp_existence
       C Code (ceval_apply E) G
       (closure_evaluation_frame_implies_goal_frame_lemma
          C Code E G)).
Qed.

(*
│
│          The negation fixed point is the Curry fixed point at `G :=
│          Bot`, since `formula_negation B = Imp B Bot`. The diagonal
│          step is goal parametric; `G := Bot` enters at the collapse
│          step.
│
*)

(*          NegationFixedPointFor(C,B) = CurryFixedPointFor(C,⊥,B).           *)

Theorem negfixp_eq_curry_bot :
  forall (C : Formula -> Prop) (B : Formula),
    NegationFixedPointFor C B <-> CurryFixedPointFor C Bot B.
Proof.
  intros C B.
  unfold NegationFixedPointFor, CurryFixedPointFor, formula_negation.
  reflexivity.
Qed.

(*
│
│          The goal-frame version of the negation fixed point is the
│          Curry theorem at `G := Bot`. Thus a code for the single
│          behavior `x ↦ ev(x,x) → ⊥` is already enough to produce `B
│          ≃_C ¬B`.
│
*)

(*                        EvC_⊥(C,ev) ⇒ ∃B. B ≃_C ¬B.                         *)

Theorem closure_goal_frame_negation_fixed_point_lemma :
  forall (C : Formula -> Prop) Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal C Code ev Bot ->
    exists B : Formula,
      NegationFixedPointFor C B.
Proof.
  intros C Code ev Hgoal_frame.
  destruct
    (curry_fixp_existence
       C Code ev Bot Hgoal_frame)
    as [B Hcurry].
  exists B.
  exact
    ((proj2 (negfixp_eq_curry_bot C B))
       Hcurry).
Qed.

(*
│
│          Minimal endpoint: the bottom goal frame produces a negation
│          fixed point.
│
*)

(*                       EvC_⊥(C,ev) ⇒ ∃B. NegFP_C(B).                        *)

Theorem eval_bottom_negfixp :
  forall (C : Formula -> Prop) Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal C Code ev Bot ->
    exists B : Formula,
      NegationFixedPointFor C B.
Proof.
  exact closure_goal_frame_negation_fixed_point_lemma.
Qed.

(*
│
│          Paper-facing adapter endpoint: a full closure evaluation
│          frame is sufficient for the current goal-restricted
│          anti-diagonal production principle at bottom.
│
*)

(*                            Eval(C) ⇒ EvC_⊥(C).                             *)

Theorem eval_full_to_eval_bottom :
  forall (C : Formula -> Prop) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureEvaluationFrameForGoal C Code (ceval_apply E) Bot.
Proof.
  intros C Code E.
  exact (closure_evaluation_frame_implies_goal_frame_lemma C Code E Bot).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                      GENERIC CURRY COLLAPSE WITH BRANCH                      │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Curry collapse — left branch. If the fixed point itself is
│          accepted, then `B → (B → G)` gives `B → G`, and a second
│          modus ponens on the same `B` gives the goal `C G`.
│
*)

(*              ModusPonens(C) ∧ (B ≃_C (B → G)) ∧ C(B) ⇒ C(G).               *)

Theorem curry_fixp_left_collapse :
  forall (C : Formula -> Prop) (G B : Formula),
    ClosureModusPonens C ->
    CurryFixedPointFor C G B ->
    C B ->
    C G.
Proof.
  intros C G B Hmp [H_B_to_BG _] HB.
  pose proof (Hmp B (Imp B G) H_B_to_BG HB) as HBG.
  exact (Hmp B G HBG HB).
Qed.

(*
│
│          Curry collapse — right branch. If `C (B → G)` is accepted,
│          then the converse implication `(B → G) → B` gives `C B`,
│          and modus ponens `B → G` with `B` gives `G`.
│
*)

(*            ModusPonens(C) ∧ (B ≃_C (B → G)) ∧ C(B → G) ⇒ C(G).             *)

Theorem curry_fixp_right_collapse :
  forall (C : Formula -> Prop) (G B : Formula),
    ClosureModusPonens C ->
    CurryFixedPointFor C G B ->
    C (Imp B G) ->
    C G.
Proof.
  intros C G B Hmp [_ H_BG_to_B] HBG.
  pose proof (Hmp (Imp B G) B H_BG_to_B HBG) as HB.
  exact (Hmp B G HBG HB).
Qed.

(*
│
│          Combined Curry collapse. From a branch disjunction `C B ∨
│          C(B→G)`, either side derives `C G`. Generalizes
│          `negfixp_decision_collapse` to arbitrary goal `G`.
│
*)

(*        ModusPonens(C) ∧ (B ≃_C (B → G)) ∧ (C(B) ∨ C(B → G)) ⇒ C(G).        *)

Theorem curry_fixp_branch_collapse :
  forall (C : Formula -> Prop) (G B : Formula),
    ClosureModusPonens C ->
    CurryFixedPointFor C G B ->
    (C B \/ C (Imp B G)) ->
    C G.
Proof.
  intros C G B Hmp Hfix Hdec.
  destruct Hdec as [HB | HBG].
  - exact (curry_fixp_left_collapse  C G B Hmp Hfix HB).
  - exact (curry_fixp_right_collapse C G B Hmp Hfix HBG).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                    GENERIC NEGATION FIXED POINT COLLAPSE                     │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          In the left branch, acceptance of the fixed point and `B →
│          ¬B` yields `¬B`; applying `¬B = B → ⊥` to `B` yields the
│          syntactic conclusion `C Bot`.
│
*)

(*                          B ≃_C ¬B ∧ C(B) ⇒ C(⊥).                           *)

Theorem negfixp_left_collapse :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    C B ->
    C Bot.
Proof.
  intros C B Hmp [H_B_to_NB _] HB.
  pose proof (Hmp B (formula_negation B) H_B_to_NB HB) as HNB.
  unfold formula_negation in HNB.
  exact (Hmp B Bot HNB HB).
Qed.

(*
│
│          In the right branch, acceptance of the fixed point's
│          negation and `¬B → B` yields `B`; the already accepted `¬B`
│          then yields the syntactic conclusion `C Bot`.
│
*)

(*                          B ≃_C ¬B ∧ C(¬B) ⇒ C(⊥).                          *)

Theorem negfixp_right_collapse :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    C (formula_negation B) ->
    C Bot.
Proof.
  intros C B Hmp [_ H_NB_to_B] HNB.
  pose proof (Hmp (formula_negation B) B H_NB_to_B HNB) as HB.
  unfold formula_negation in HNB.
  exact (Hmp B Bot HNB HB).
Qed.

(*
│
│          `negfixp_decision_collapse` combines the two modus ponens
│          branch lemmas for a supplied branch disjunction. It
│          consumes a concrete `C B \/ C (¬B)` choice and derives `C
│          Bot`; no consistency hypothesis enters this collapse step.
│
*)

(*            ModusPonens(C) ∧ (B ≃_C ¬B) ∧ (C(B) ∨ C(¬B)) ⇒ C(⊥).            *)

Theorem local_branch_collapse :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    ClosureLocalExcludedMiddle C B ->
    C Bot.
Proof.
  intros C B Hmp Hfix Hdec.
  destruct Hdec as [HB | HNB].
  - exact
      (negfixp_left_collapse
         C B Hmp Hfix HB).
  - exact
      (negfixp_right_collapse
         C B Hmp Hfix HNB).
Qed.

(*
│
│          Compatibility spelling retained for older clients: the
│          supplied branch disjunction is the local excluded-middle
│          datum.
│
*)

Theorem negfixp_decision_collapse :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    (C B \/ C (formula_negation B)) ->
    C Bot.
Proof.
  exact local_branch_collapse.
Qed.

(*
│
│          `negfixp_lem_collapse` obtains the Rocq-level disjunction
│          between the two accepted object-language branches from
│          `ClosureExcludedMiddle C` and routes it through the
│          explicit branch-collapse adapter. No object-language
│          disjunction connective is present.
│
*)

(*       ModusPonens(C) ∧ (B ≃_C ¬B) ∧ ClosureExcludedMiddle(C) ⇒ C(⊥).       *)

Theorem negfixp_lem_collapse :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    ClosureExcludedMiddle C ->
    C Bot.
Proof.
  intros C B Hmp Hfix Hlem.
  apply
    (local_branch_collapse
       C B Hmp Hfix).
  exact (closure_lem_to_local_lemma C B Hlem).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         GENERIC EVALUATION COLLAPSE                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Goal-frame collapse is the positive consequence at bottom:
│          the minimal frame `EvC_⊥`, closure-level excluded middle,
│          and modus ponens derive `⊥` inside the same closure
│          predicate. No consistency hypothesis is used.
│
*)

(*          ModusPonens(C) ∧ EvC_⊥(C,ev) ∧ ExcludedMiddle(C) ⇒ C(⊥).          *)

Theorem closure_goal_frame_excluded_middle_collapses_lemma :
  forall (C : Formula -> Prop) Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal C Code ev Bot ->
    ClosureModusPonens C ->
    ClosureExcludedMiddle C ->
    exists B : Formula,
      NegationFixedPointFor C B /\
      (C B \/ C (formula_negation B)) /\
      C Bot.
Proof.
  intros C Code ev Hgoal_frame Hmp Hlem.
  destruct
    (closure_goal_frame_negation_fixed_point_lemma
       C Code ev Hgoal_frame)
    as [B Hfix].
  pose proof (Hlem B) as Hdec.
  exists B.
  split.
  - exact Hfix.
  - split.
    + exact Hdec.
    + exact
        (negfixp_decision_collapse
           C B Hmp Hfix Hdec).
Qed.

(*
│
│          The full-frame excluded-middle collapse is the corollary
│          obtained by extracting the bottom goal frame from a
│          universal `ClosureEvaluationFrame`.
│
*)

(*        ModusPonens(C) ∧ EvalComplete(C) ∧ ExcludedMiddle(C) ⇒ C(⊥).        *)

Theorem lem_collapse :
  forall (C : Formula -> Prop) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureModusPonens C ->
    ClosureExcludedMiddle C ->
    exists B : Formula,
      NegationFixedPointFor C B /\
      (C B \/ C (formula_negation B)) /\
      C Bot.
Proof.
  intros C Code E Hmp Hlem.
  exact
    (closure_goal_frame_excluded_middle_collapses_lemma
       C Code (ceval_apply E)
       (closure_evaluation_frame_implies_goal_frame_lemma
          C Code E Bot)
       Hmp Hlem).
Qed.

(*
│
│          The goal-frame decision collapse first converts a Boolean
│          classifier to closure-level excluded middle, then applies
│          the minimal bottom-frame collapse theorem.
│
*)

(*         ModusPonens(C) ∧ EvC_⊥(C,ev) ∧ ClosureDecision(C) ⇒ C(⊥).          *)

Theorem closure_goal_frame_decision_collapses_lemma :
  forall (C : Formula -> Prop) Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal C Code ev Bot ->
    ClosureModusPonens C ->
    ClosureDecision C ->
    exists B : Formula,
      NegationFixedPointFor C B /\
      (C B \/ C (formula_negation B)) /\
      C Bot.
Proof.
  intros C Code ev Hgoal_frame Hmp D.
  exact
    (closure_goal_frame_excluded_middle_collapses_lemma
       C Code ev Hgoal_frame Hmp
       (decision_to_lem C D)).
Qed.

(*
│
│          The full-frame decision collapse is the universal-frame
│          corollary of the goal-frame decision theorem.
│
*)

(*       ModusPonens(C) ∧ EvalComplete(C) ∧ ClosureDecision(C) ⇒ C(⊥).        *)

Theorem decision_collapse :
  forall (C : Formula -> Prop) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureModusPonens C ->
    ClosureDecision C ->
    exists B : Formula,
      NegationFixedPointFor C B /\
      (C B \/ C (formula_negation B)) /\
      C Bot.
Proof.
  intros C Code E Hmp D.
  exact
    (closure_goal_frame_decision_collapses_lemma
       C Code (ceval_apply E)
       (closure_evaluation_frame_implies_goal_frame_lemma
          C Code E Bot)
       Hmp D).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           REGULATOR SPECIALIZATION                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The regulator specialization below uses only M001's closure
│          modus-ponens lemma.
│
*)

(*
│
│          `RegulatorNegationFixedPoint` is the M001 specialization of
│          the generic negation fixed-point predicate. It abbreviates
│          `NegationFixedPointFor` at the closure predicate
│          `RegulatorClosure profile T Gamma`; it adds no new semantic
│          principle.
│
*)

(*               RegulatorNegationFixedPoint(profile,T,Γ,B) ≔ B               *)
(*                   ≃_{RegulatorClosure(profile,T,Γ)} ¬B.                    *)

Definition RegulatorNegationFixedPoint
    (profile : RegulatorLogicProfile)
    (T : AxiomSet)
    (Gamma : Context)
    (B : Formula) : Prop :=
  NegationFixedPointFor (RegulatorClosure profile T Gamma) B.

(*
│
│          `regulator_negfixp_existence` is the M001 instance of the
│          generic diagonal step. A regulated evaluation frame is
│          first read as a closure evaluation frame, and the result is
│          only the existence of a formula equivalent to its
│          object-level negation.
│
*)

(*             RegulatorEvaluationComplete(profile,T,Γ) ⇒ ∃ B, B              *)
(*                   ≃_{RegulatorClosure(profile,T,Γ)} ¬B.                    *)

Theorem regulator_negfixp_existence :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code),
    exists B : Formula,
      RegulatorNegationFixedPoint profile T Gamma B.
Proof.
  intros profile T Gamma Code E.
  exact
    (negfixp_existence
       (RegulatorClosure profile T Gamma)
       Code
       (regulator_closure_evaluation_frame
          profile T Gamma Code E)).
Qed.

(*
│
│          The regulator left branch specializes the generic left
│          modus ponens path: from `RegulatorClosure B` and the
│          fixed-point implication `B → ¬B`, M001 modus ponens derives
│          `RegulatorClosure (¬B)`, and a second modus ponens step
│          derives `RegulatorClosure Bot`.
│
*)

(*RegulatorNegationFixedPoint(profile,T,Γ,B) ∧ RegulatorClosure(profile,T,Γ,B)*)
(*                     ⇒ RegulatorClosure(profile,T,Γ,⊥).                     *)

Theorem regulator_negfixp_left_collapse :
  forall profile T Gamma B,
    RegulatorNegationFixedPoint profile T Gamma B ->
    RegulatorClosure profile T Gamma B ->
    RegulatorClosure profile T Gamma Bot.
Proof.
  intros profile T Gamma B Hfix HB.
  exact
    (negfixp_left_collapse
       (RegulatorClosure profile T Gamma)
       B
       (regulator_closure_modus_ponens_lemma profile T Gamma)
       Hfix
       HB).
Qed.

(*
│
│          The regulator right branch specializes the generic right
│          modus ponens path: from `RegulatorClosure (¬B)` and the
│          fixed-point implication `¬B → B`, M001 modus ponens derives
│          `RegulatorClosure B`; the already accepted negation then
│          yields `RegulatorClosure Bot`.
│
*)

(*                RegulatorNegationFixedPoint(profile,T,Γ,B) ∧                *)
(*    RegulatorClosure(profile,T,Γ,¬B) ⇒ RegulatorClosure(profile,T,Γ,⊥).     *)

Theorem regulator_negfixp_right_collapse :
  forall profile T Gamma B,
    RegulatorNegationFixedPoint profile T Gamma B ->
    RegulatorClosure profile T Gamma (formula_negation B) ->
    RegulatorClosure profile T Gamma Bot.
Proof.
  intros profile T Gamma B Hfix HNB.
  exact
    (negfixp_right_collapse
       (RegulatorClosure profile T Gamma)
       B
       (regulator_closure_modus_ponens_lemma profile T Gamma)
       Hfix
       HNB).
Qed.

Theorem negfixp_branch_collapse :
  forall profile T Gamma B,
    RegulatorNegationFixedPoint profile T Gamma B ->
    (RegulatorClosure profile T Gamma B \/
     RegulatorClosure profile T Gamma (formula_negation B)) ->
    RegulatorClosure profile T Gamma Bot.
Proof.
  intros profile T Gamma B Hfix Hdec.
  exact
    (negfixp_decision_collapse
       (RegulatorClosure profile T Gamma)
       B
       (regulator_closure_modus_ponens_lemma profile T Gamma)
       Hfix
       Hdec).
Qed.

Theorem regulator_lem_collapse :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code),
    RegulatorClosureExcludedMiddle profile T Gamma ->
    exists B : Formula,
      RegulatorNegationFixedPoint profile T Gamma B /\
      (RegulatorClosure profile T Gamma B \/
       RegulatorClosure profile T Gamma (formula_negation B)) /\
      RegulatorClosure profile T Gamma Bot.
Proof.
  intros profile T Gamma Code E Hlem.
  exact
    (lem_collapse
       (RegulatorClosure profile T Gamma)
       Code
       (regulator_closure_evaluation_frame
          profile T Gamma Code E)
       (regulator_closure_modus_ponens_lemma profile T Gamma)
       ((proj1 (regulator_lem_iff_closure_lem profile T Gamma)) Hlem)).
Qed.

(*
│
│          Regulated evaluation supplies the fixed point and
│          `RegulatorDecision` supplies the collapsing branch.
│
*)

Theorem regulator_decision_collapse :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code),
    RegulatorDecision profile T Gamma ->
    exists B : Formula,
      RegulatorNegationFixedPoint profile T Gamma B /\
      (RegulatorClosure profile T Gamma B \/
       RegulatorClosure profile T Gamma (formula_negation B)) /\
      RegulatorClosure profile T Gamma Bot.
Proof.
  intros profile T Gamma Code E D.
  exact
    (regulator_lem_collapse
       profile T Gamma Code E
       (regulator_decision_to_lem profile T Gamma D)).
Qed.

Theorem aporetic_lemma :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code),
    RegulatorDecision profile T Gamma ->
    exists B : Formula,
      RegulatorNegationFixedPoint profile T Gamma B /\
      (RegulatorClosure profile T Gamma B \/
       RegulatorClosure profile T Gamma (formula_negation B)) /\
      RegulatorClosure profile T Gamma Bot.
Proof.
  intros profile T Gamma Code E D.
  exact
    (regulator_decision_collapse
       profile T Gamma Code E D).
Qed.

Theorem aporetic_status_yes_collapses_lemma :
  forall profile T Gamma Code
         (E : RegulatorClosureEvaluationFrame profile T Gamma Code)
         (excluded_middle_status : Formula),
    YesBranchDecides profile T Gamma excluded_middle_status ->
    RegulatorClosure profile T Gamma excluded_middle_status ->
    exists B : Formula,
      RegulatorNegationFixedPoint profile T Gamma B /\
      (RegulatorClosure profile T Gamma B \/
       RegulatorClosure profile T Gamma (formula_negation B)) /\
      RegulatorClosure profile T Gamma Bot.
Proof.
  intros profile T Gamma Code E excluded_middle_status Hyes Hstatus.
  apply
    (regulator_decision_collapse
       profile T Gamma Code E).
  exact (Hyes Hstatus).
Qed.
