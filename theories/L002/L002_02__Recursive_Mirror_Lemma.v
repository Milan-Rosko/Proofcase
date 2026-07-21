(*L002_02__Recursive_Mirror_Lemma.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / L002_02__Recursive_Mirror_Lemma                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Recursive-mirror layer for L002. We iterate a formula transformer and prove
  pointwise that the same irrefutability and recognition-opacity obstruction
  holds at every finite depth satisfying the supplied adequacy conditions, or
  from a supplied seed plus a position-preservation law. This single
  all-finite-depth theorem does not assert an actual infinite execution,
  divergence, stack overflow, crash, finite-state recurrence, or
  psychological process; those require an operational model connecting
  formula iteration to concrete dynamics.

*)

From L002 Require Export L002_01__Mirror_Unrefutability.
From Stdlib Require Import Lia.

(*
│
│          `recursive_mirror_formula depth mirror_step chi` applies
│          `mirror_step` to `chi` exactly `depth` times.
│
*)

Fixpoint recursive_mirror_formula
    (depth : nat)
    (mirror_step : Formula -> Formula)
    (chi : Formula) : Formula :=
  match depth with
  | O => chi
  | S depth' =>
      mirror_step
        (recursive_mirror_formula depth' mirror_step chi)
  end.

(*
│
│          Recursive-mirror adequacy requires every finite formula
│          iterate to be a one-way external mirror position.
│
*)

Definition RecursiveMirrorAdequacy
    (M : RegulatorTheory)
    (Gamma : Context)
    (mirror_step : Formula -> Formula)
    (chi : Formula) : Prop :=
  forall depth : nat,
    ExternalMirrorPosition M Gamma
      (recursive_mirror_formula depth mirror_step chi).

(*
│
│          A mirror step preserves external fixed-point position when
│          it maps every externally fixed formula to another
│          externally fixed formula.
│
*)

Definition MirrorStepPreservesExternalFixedPoints
    (M : RegulatorTheory)
    (Gamma : Context)
    (mirror_step : Formula -> Formula) : Prop :=
  forall A : Formula,
    ExternalFixedPoint M Gamma A ->
    ExternalFixedPoint M Gamma (mirror_step A).

Definition MirrorStepPreservesExternalMirrorPositions
    (M : RegulatorTheory)
    (Gamma : Context)
    (mirror_step : Formula -> Formula) : Prop :=
  forall A : Formula,
    ExternalMirrorPosition M Gamma A ->
    ExternalMirrorPosition M Gamma (mirror_step A).

(*
│
│          The implication-reflection mirror wraps `A` as `(A -> A) ->
│          A`. It is syntactically non-identity while remaining
│          interderivable with `A` in the minimal K/S checked theory.
│
*)

Definition implication_reflection_mirror (A : Formula) : Formula :=
  Imp (Imp A A) A.

Theorem implication_reflection_mirror_intro :
  forall (M : RegulatorTheory) (Gamma : Context) (A : Formula),
    regulator_theory_checked_derivable M Gamma
      (Imp A (implication_reflection_mirror A)).
Proof.
  intros M Gamma A.
  unfold implication_reflection_mirror.
  apply regulator_theory_axiom_checked_derivable_lemma.
  apply available_axiom_bool_k_lemma.
Qed.

Theorem implication_reflection_mirror_elim :
  forall (M : RegulatorTheory) (Gamma : Context) (A : Formula),
    regulator_theory_checked_derivable M Gamma
      (Imp (implication_reflection_mirror A) A).
Proof.
  intros M Gamma A.
  apply assumption_discharge.
  apply regulator_theory_checked_derivable_mp_lemma with (A := Imp A A).
  - exact (assumption_intro M Gamma (implication_reflection_mirror A)).
  - apply checked_derivable_under_assumption.
    apply assumption_discharge.
    exact (assumption_intro M Gamma A).
Qed.

(*
│
│          The implication-reflection mirror preserves negation fixed
│          points. The proof uses its two checked implication
│          directions and explicitly transports the fixed-point
│          derivations through the wrapper.
│
*)

Theorem implication_reflection_mirror_preserves_external_fixed_points :
  forall (M : RegulatorTheory) (Gamma : Context),
    MirrorStepPreservesExternalFixedPoints
      M Gamma implication_reflection_mirror.
Proof.
  intros M Gamma A [Hforward Hbackward].
  set (W := implication_reflection_mirror A).
  assert (HAW : regulator_theory_checked_derivable M Gamma (Imp A W)).
  { unfold W. exact (implication_reflection_mirror_intro M Gamma A). }
  assert (HWA : regulator_theory_checked_derivable M Gamma (Imp W A)).
  { unfold W. exact (implication_reflection_mirror_elim M Gamma A). }
  split.
  - assert (HnegW : regulator_theory_checked_derivable M Gamma (formula_negation W)).
    {
      apply assumption_discharge.
      apply regulator_theory_checked_derivable_mp_lemma with (A := A).
      - apply regulator_theory_checked_derivable_mp_lemma with (A := A).
        + apply checked_derivable_under_assumption. exact Hforward.
        + apply regulator_theory_checked_derivable_mp_lemma with (A := W).
          * apply checked_derivable_under_assumption. exact HWA.
          * exact (assumption_intro M Gamma W).
      - apply regulator_theory_checked_derivable_mp_lemma with (A := W).
        + apply checked_derivable_under_assumption. exact HWA.
        + exact (assumption_intro M Gamma W).
    }
    apply regulator_theory_checked_derivable_mp_lemma
      with (A := formula_negation W).
    + apply regulator_theory_axiom_checked_derivable_lemma.
      apply available_axiom_bool_k_lemma.
    + exact HnegW.
  - apply assumption_discharge.
    apply regulator_theory_checked_derivable_mp_lemma with (A := A).
    + apply checked_derivable_under_assumption. exact HAW.
    + apply regulator_theory_checked_derivable_mp_lemma
        with (A := formula_negation A).
      * apply checked_derivable_under_assumption. exact Hbackward.
      * apply assumption_discharge.
        apply regulator_theory_checked_derivable_mp_lemma with (A := W).
        { apply regulator_theory_assumption_checked_derivable_lemma.
          apply ctx_mem_bool_extend_preserve_lemma.
          apply ctx_mem_bool_extend_self_lemma. }
        { apply regulator_theory_checked_derivable_mp_lemma with (A := A).
          * apply checked_derivable_under_assumption.
            apply checked_derivable_under_assumption.
            exact HAW.
          * exact
              (assumption_intro
                 M (ctx_extend (formula_negation W) Gamma) A). }
Qed.

Theorem implication_reflection_mirror_preserves_external_mirror_positions :
  forall (M : RegulatorTheory) (Gamma : Context),
    MirrorStepPreservesExternalMirrorPositions
      M Gamma implication_reflection_mirror.
Proof.
  intros M Gamma A Hbackward.
  set (W := implication_reflection_mirror A).
  assert (HAW : regulator_theory_checked_derivable M Gamma (Imp A W)).
  { unfold W. exact (implication_reflection_mirror_intro M Gamma A). }
  apply assumption_discharge.
  apply regulator_theory_checked_derivable_mp_lemma with (A := A).
  - apply checked_derivable_under_assumption.
    exact HAW.
  - apply regulator_theory_checked_derivable_mp_lemma
      with (A := formula_negation A).
    + apply checked_derivable_under_assumption.
      exact Hbackward.
    + apply assumption_discharge.
      apply regulator_theory_checked_derivable_mp_lemma with (A := W).
      { apply regulator_theory_assumption_checked_derivable_lemma.
        apply ctx_mem_bool_extend_preserve_lemma.
        apply ctx_mem_bool_extend_self_lemma. }
      { apply regulator_theory_checked_derivable_mp_lemma with (A := A).
        - apply checked_derivable_under_assumption.
          apply checked_derivable_under_assumption.
          exact HAW.
        - exact
            (assumption_intro
               M (ctx_extend (formula_negation W) Gamma) A). }
Qed.

(*
│
│          A recursive-mirror position requires every finite formula
│          iterate to satisfy `AsIF`.
│
*)

Definition RecursiveMirrorPosition
    (M : RegulatorTheory)
    (Gamma : Context)
    (mirror_step : Formula -> Formula)
    (chi : Formula) : Prop :=
  forall depth : nat,
    AsIF M Gamma
      (recursive_mirror_formula depth mirror_step chi).

(*
│
│          The zero-depth recursive mirror is the seed formula.
│
*)

Theorem recursive_mirror_formula_zero :
  forall mirror_step chi,
    recursive_mirror_formula O mirror_step chi = chi.
Proof.
  reflexivity.
Qed.

(*
│
│          A successor-depth recursive mirror is one `mirror_step`
│          applied to the preceding iterate.
│
*)

Theorem recursive_mirror_formula_successor :
  forall depth mirror_step chi,
    recursive_mirror_formula (S depth) mirror_step chi =
    mirror_step (recursive_mirror_formula depth mirror_step chi).
Proof.
  reflexivity.
Qed.

(*
│
│          One externally fixed seed and a fixed-point-preserving
│          mirror step generate external fixed-point adequacy at every
│          finite depth.
│
*)

Theorem recursive_mirror_adequacy_from_seed :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorStepPreservesExternalMirrorPositions M Gamma mirror_step ->
    RecursiveMirrorAdequacy M Gamma mirror_step chi.
Proof.
  intros M Gamma mirror_step chi Hseed Hpreserves depth.
  induction depth as [|depth IH].
  - exact Hseed.
  - simpl.
    exact (Hpreserves _ IH).
Qed.

(*
│
│          Adequacy and M-consistency make every finite mirror iterate
│          internally non-refutable.
│
*)

Theorem recursive_mirror_irrefutability :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    RecursiveMirrorPosition M Gamma mirror_step chi.
Proof.
  intros M Gamma mirror_step chi Hadequate Hconsistent depth.
  exact
    (external_mirror_position_forces_asif
       M Gamma
       (recursive_mirror_formula depth mirror_step chi)
       (Hadequate depth)
       Hconsistent).
Qed.

(*
│
│          For a fixed symbolic regulator, every adequate mirror
│          iterate satisfies `AsIF` and excludes adequate internal
│          recognition.
│
*)

Theorem recursive_mirror_lemma :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth : nat,
      ~ InternalFixedPointRecognition
          M Gamma
          (fixed_recognition_claim S)
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  intros Slambda M Gamma S mirror_step chi Hadequate.
  pose proof
    (outer_consistency_implies_mirror_consistency
       Slambda M Gamma
       (fixed_regulator_inclusion S)
       (fixed_regulator_consistency S)) as HMconsistent.
  split.
  - exact
      (recursive_mirror_irrefutability
         M Gamma mirror_step chi Hadequate HMconsistent).
  - intro depth.
    exact
      (proj2
         (fixed_regulator_mirror_opacity
            Slambda M Gamma S
            (recursive_mirror_formula depth mirror_step chi)
            (Hadequate depth))).
Qed.

(*
│
│          The coded Recursive Mirror Lemma uses only M-consistency
│          and the concrete recognition regulator; no legacy
│          formula-valued recognition coding or enclosing
│          fixed-regulator record is required.
│
*)

Theorem coded_recursive_mirror_lemma :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth : nat,
      ~ CodedRecognitionAccepted M Gamma
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  intros M Gamma mirror_step chi Hadequate Hconsistent.
  split.
  - exact
      (recursive_mirror_irrefutability
         M Gamma mirror_step chi Hadequate Hconsistent).
  - intro depth.
    exact
      (coded_recognition_opacity
         M Gamma
         (recursive_mirror_formula depth mirror_step chi)
         (Hadequate depth) Hconsistent).
Qed.

(*
│
│          The seed-based Recursive Mirror Lemma derives the all-depth
│          result from one external mirror position and a reusable
│          preservation law for the supplied mirror step.
│
*)

Theorem recursive_mirror_lemma_from_seed :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorStepPreservesExternalMirrorPositions M Gamma mirror_step ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth : nat,
      ~ InternalFixedPointRecognition
          M Gamma
          (fixed_recognition_claim S)
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  intros Slambda M Gamma S mirror_step chi Hseed Hpreserves.
  apply recursive_mirror_lemma.
  exact
    (recursive_mirror_adequacy_from_seed
       M Gamma mirror_step chi Hseed Hpreserves).
Qed.

Theorem coded_recursive_mirror_lemma_from_seed :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorStepPreservesExternalMirrorPositions M Gamma mirror_step ->
    MirrorConsistent M Gamma ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth : nat,
      ~ CodedRecognitionAccepted M Gamma
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  intros M Gamma mirror_step chi Hseed Hpreserves Hconsistent.
  apply coded_recursive_mirror_lemma.
  - exact
      (recursive_mirror_adequacy_from_seed
         M Gamma mirror_step chi Hseed Hpreserves).
  - exact Hconsistent.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         OPERATIONAL CONTROL RE-ENTRY                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `RecursiveControlProcess` supplies a total response trace
│          and soundness bridges for its `yes` and `no` outputs.
│          Re-entry is an operational tag: at depth `n`, the next
│          question is definitionally the `(S n)` mirror iterate.
│
*)

Record RecursiveControlProcess
    (M : RegulatorTheory)
    (Gamma : Context)
    (mirror_step : Formula -> Formula)
    (chi : Formula) : Type := {
  recursive_control_response_at : nat -> ControlResponse;
  recursive_control_yes_sound :
    forall depth : nat,
      recursive_control_response_at depth = control_response_yes ->
      regulator_theory_checked_derivable M Gamma
        (recursive_mirror_formula depth mirror_step chi);
  recursive_control_no_sound :
    forall depth : nat,
      recursive_control_response_at depth = control_response_no ->
      regulator_theory_checked_derivable M Gamma
        (formula_negation
           (recursive_mirror_formula depth mirror_step chi))
}.

Arguments recursive_control_response_at
  {M Gamma mirror_step chi} _ _.
Arguments recursive_control_yes_sound
  {M Gamma mirror_step chi} _ _ _.
Arguments recursive_control_no_sound
  {M Gamma mirror_step chi} _ _ _.

Definition ControlAnswersYesAt
    {M Gamma mirror_step chi}
    (process : RecursiveControlProcess M Gamma mirror_step chi)
    (depth : nat) : Prop :=
  recursive_control_response_at process depth = control_response_yes.

Definition ControlReentersAt
    {M Gamma mirror_step chi}
    (process : RecursiveControlProcess M Gamma mirror_step chi)
    (depth : nat) : Prop :=
  recursive_control_response_at process depth = control_response_reenter.

Definition EventuallyAnswersYes
    {M Gamma mirror_step chi}
    (process : RecursiveControlProcess M Gamma mirror_step chi) : Prop :=
  exists depth : nat,
    ControlAnswersYesAt process depth.

Definition ReentersThrough
    {M Gamma mirror_step chi}
    (process : RecursiveControlProcess M Gamma mirror_step chi)
    (fuel : nat) : Prop :=
  forall depth : nat,
    depth <= fuel ->
    ControlReentersAt process depth.

Definition ReentersForever
    {M Gamma mirror_step chi}
    (process : RecursiveControlProcess M Gamma mirror_step chi) : Prop :=
  forall depth : nat,
    ControlReentersAt process depth.

(*
│
│          `ControlOutcomeDecidable` is an additional operational
│          specification deciding whether an unbounded process ever
│          answers `yes`. It is not derived from the finite response
│          alphabet or from proof-theoretic consistency.
│
*)

Definition ControlOutcomeDecidable
    {M Gamma mirror_step chi}
    (process : RecursiveControlProcess M Gamma mirror_step chi) : Prop :=
  EventuallyAnswersYes process \/
  ~ EventuallyAnswersYes process.

(*
│
│          Recursive mirror adequacy and model consistency exclude the
│          negative response at every depth.
│
*)

Theorem recursive_control_no_response_impossible :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula)
         (process : RecursiveControlProcess M Gamma mirror_step chi),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    forall depth : nat,
      recursive_control_response_at process depth <>
      control_response_no.
Proof.
  intros M Gamma mirror_step chi process
    Hadequate Hconsistent depth Hno.
  pose proof
    (external_mirror_position_forces_asif
       M Gamma
       (recursive_mirror_formula depth mirror_step chi)
       (Hadequate depth) Hconsistent) as Hasif.
  apply Hasif.
  exact (recursive_control_no_sound process depth Hno).
Qed.

Theorem recursive_control_response_yes_or_reenters :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula)
         (process : RecursiveControlProcess M Gamma mirror_step chi),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    forall depth : nat,
      ControlAnswersYesAt process depth \/
      ControlReentersAt process depth.
Proof.
  intros M Gamma mirror_step chi process
    Hadequate Hconsistent depth.
  unfold ControlAnswersYesAt, ControlReentersAt.
  destruct (recursive_control_response_at process depth) eqn:Hresponse.
  - left. reflexivity.
  - exfalso.
    exact
      (recursive_control_no_response_impossible
         M Gamma mirror_step chi process
         Hadequate Hconsistent depth Hresponse).
  - right. reflexivity.
Qed.

(*
│
│          Constructive finite form of `yes` or recursion: at every
│          supplied observation bound, either a positive answer has
│          appeared within the bound or every stage through the bound
│          is a re-entry.
│
*)

Theorem finite_yes_or_recursive_reentry :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula)
         (process : RecursiveControlProcess M Gamma mirror_step chi),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    forall fuel : nat,
      (exists depth : nat,
         depth <= fuel /\
         ControlAnswersYesAt process depth) \/
      ReentersThrough process fuel.
Proof.
  intros M Gamma mirror_step chi process Hadequate Hconsistent fuel.
  induction fuel as [|fuel IH].
  - destruct
      (recursive_control_response_yes_or_reenters
         M Gamma mirror_step chi process
         Hadequate Hconsistent O) as [Hyes | Hreenter].
    + left. exists O. split; [lia | exact Hyes].
    + right. intros depth Hdepth.
      assert (depth = O) by lia.
      subst depth.
      exact Hreenter.
  - destruct IH as [[depth [Hdepth Hyes]] | Hthrough].
    + left. exists depth. split; [lia | exact Hyes].
    + destruct
        (recursive_control_response_yes_or_reenters
           M Gamma mirror_step chi process
           Hadequate Hconsistent (S fuel)) as [Hyes | Hreenter].
      * left. exists (S fuel). split; [lia | exact Hyes].
      * right. intros depth Hdepth.
        destruct (Nat.eq_dec depth (S fuel)) as [Hequal | Hneq].
        -- subst depth. exact Hreenter.
        -- apply Hthrough. lia.
Qed.

(*
│
│          The unbounded disjunction requires the explicit
│          outcome-decidability bridge. Under that bridge, absence of
│          an eventual `yes` and pointwise exclusion of `no` force
│          reflective re-entry at every finite depth.
│
*)

Theorem yes_or_recursive_reentry :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula)
         (process : RecursiveControlProcess M Gamma mirror_step chi),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    ControlOutcomeDecidable process ->
    EventuallyAnswersYes process \/
    ReentersForever process.
Proof.
  intros M Gamma mirror_step chi process
    Hadequate Hconsistent [Heventual | Hnever].
  - left. exact Heventual.
  - right. intro depth.
    destruct
      (recursive_control_response_yes_or_reenters
         M Gamma mirror_step chi process
         Hadequate Hconsistent depth) as [Hyes | Hreenter].
    + exfalso. apply Hnever. exists depth. exact Hyes.
    + exact Hreenter.
Qed.
