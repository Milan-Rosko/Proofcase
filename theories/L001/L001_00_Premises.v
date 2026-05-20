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

  L001 begins where M001 stops. It imports only the frozen M001 evaluation
  API and interprets the regulated evaluation fixed-point engine as a
  statement about excluded-middle status at the regulator level. L001 may use
  Aporetic and status vocabulary; it does not modify M001 or import M001
  internal files.

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
│          A regulator that merely lacks a proof of excluded middle
│          remains constructively silent. A regulator that decides the
│          status of excluded middle, however, reifies the question
│          into behavior. The first formal branch is the decision
│          branch: regulated evaluation closure yields a formula `B`
│          equivalent, under regulator derivability, to its own
│          negation. A total regulator decision must classify `B`;
│          either classification derives `Bot`. Consistency is not
│          part of that collapse mechanism, and is used only later as
│          an obstruction hypothesis.
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
│          `ClosureEquiv C A B` is equivalence inside the closure
│          predicate: both object-level implications are accepted by
│          `C`. It is not meta-level equality of formulas and not
│          semantic equivalence in a model. The whole closure layer
│          below requires only a constructive closure predicate `C :
│          Formula -> Prop`, an implication-induced equivalence,
│          evaluation completeness up to that equivalence, and modus
│          ponens closure when collapse is extracted.
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
│          `ClosureExcludedMiddle C` is excluded-middle status inside
│          the closure predicate: every formula is either accepted by
│          `C`, or its object-level negation is accepted by `C`. This
│          is not Rocq's excluded middle and does not assert `A \/ ~
│          A` for arbitrary propositions.
│
*)

(*               ClosureExcludedMiddle(C) ≔ ∀ A, C(A) ∨ C(¬A).                *)

Definition ClosureExcludedMiddle
    (C : Formula -> Prop) : Prop :=
  forall A : Formula,
    C A \/ C (formula_negation A).

(*
│
│          `ClosureModusPonens C` says that the closure predicate is
│          closed under object-level modus ponens. It transports
│          accepted implications and accepted antecedents to accepted
│          consequents; it is not a global rule for arbitrary Rocq
│          propositions.
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
│          a closure predicate: if the object-level bottom formula is
│          accepted, the ambient Rocq context becomes contradictory.
│          It is not used to build collapse, only to turn an already
│          constructed `C Bot` into obstruction.
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
│          object-level negation imply each other under `C`. It does
│          not assert semantic self-negation or a Rocq-level
│          contradiction by itself.
│
*)

(*                   NegationFixedPointFor(C,B) ≔ B ≃_C ¬B.                   *)

Definition NegationFixedPointFor
    (C : Formula -> Prop)
    (B : Formula) : Prop :=
  ClosureEquiv C B (formula_negation B).

(*
│
│          `ClosureDecision C` is a total Boolean status classifier.
│          The true branch certifies `C A`; the false branch certifies
│          `C (¬A)`. This is stronger than `ClosureExcludedMiddle C`,
│          which supplies only a Prop-level disjunction.
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
│          `ClosureEvaluationFrame C Code` is the generic evaluation
│          interface for the closure theorem. It supplies coded
│          formulas and closure-level completeness up to
│          `ClosureEquiv`; it is not a semantic truth definition and
│          not a model of formulas.
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
│          `ClosureEvaluationFrameForGoal C Code ev G` is the minimal
│          evaluation-completeness fragment needed for the Curry fixed
│          point at goal `G`. It requires a code for the single
│          diagonal behavior `x ↦ ev x x → G`, not a universal name
│          for every behavior.
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
│          predicate. It is the M001 instance needed by the later
│          collapse proofs, not a separate primitive Aporetic theorem.
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
│          `RegulatorClosureExcludedMiddle` is the specialization of
│          `ClosureExcludedMiddle` to `RegulatorClosure profile T
│          Gamma`. It is regulator-level excluded-middle status: every
│          formula is accepted by the regulator predicate, or its
│          object-level negation is accepted. This is not Rocq's
│          excluded middle.
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
│          `RegulatorDecision` is a total Boolean classifier for the
│          M001 regulator instance. The true branch certifies
│          `RegulatorClosure profile T Gamma A`; the false branch
│          certifies `RegulatorClosure profile T Gamma (¬A)`. This is
│          stronger than `RegulatorClosureExcludedMiddle`, which
│          supplies only a Prop-level disjunction.
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
│          `YesBranchDecides` reads acceptance of a presented
│          excluded-middle-status formula as the existence of a total
│          regulator decision. The yes-branch obstruction theorems
│          take this conversion as a hypothesis, so the collapse
│          argument never needs to construct the decision itself.
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
│          `RegulatorRefutation` is the negative-side classifier: a
│          true Boolean result certifies acceptance of an object-level
│          negation by `RegulatorClosure`. No false-branch
│          completeness is asserted, so this is genuinely weaker than
│          `RegulatorDecision`; the refutation-non-collapse witness in
│          `L001_02` exhibits the constructive separation.
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
│          negations into accepted formulas. L001 does not assume this
│          bridge globally; the no-branch obstruction theorems in
│          `L001_02` take it as an explicit hypothesis.
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
