(*L002_95_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / L002_95_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Public API for L002. `L002_CORE_CONTRACT` contains the minimal fixed-point,
  mirror, coded-recognition, and finite-depth results. The legacy `WITNESS`
  preserves the earlier broad operational and response-law contract.

*)

From L002 Require Export L002_03__Symbolic_Regulation.

(*
│
│          The preferred irrefutability contract states that a one-way
│          mirror position and M-consistency imply `AsIF`.
│
*)

Definition ASIF_FROM_EXTERNAL_MIRROR_POSITION_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AsIF M Gamma chi.

Definition LOCAL_MIRROR_IRREFUTABILITY_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorLocallyConsistent M Gamma chi ->
    AsIF M Gamma chi.

Definition GOAL_FRAME_EXTERNAL_FIXED_POINT_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal
      (regulator_theory_checked_derivable M Gamma)
      Code ev Bot ->
    exists chi : Formula,
      ExternalFixedPoint M Gamma chi.

Definition FULL_FIXED_POINT_COLLAPSE_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalFixedPoint M Gamma chi ->
    regulator_theory_checked_derivable M Gamma Bot.

(*
│
│          The concrete recognition contract excludes finite checked
│          proof certificates whose literal target is the refutation
│          of an external fixed point.
│
*)

Definition CHECKED_REFUTATION_RECOGNITION_OPACITY_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    CheckedRefutationRecognitionCertificate M Gamma chi ->
    False.

(*
│
│          The coded recognition contract excludes acceptance of a
│          first-class fixed-point claim by L002's finite certificate
│          regulator.
│
*)

Definition CODED_RECOGNITION_OPACITY_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    ~ CodedRecognitionAccepted M Gamma chi.

Definition LOCAL_CODED_RECOGNITION_OPACITY_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorLocallyConsistent M Gamma chi ->
    ~ CodedRecognitionAccepted M Gamma chi.

Definition CODED_RECOGNITION_EVIDENCE_SPECIFICATION_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    CodedRecognitionAccepted M Gamma A <->
    regulator_theory_checked_derivable M Gamma
      (coded_recognition_evidence_formula A).

(*
│
│          Stronger explanatory specification: in M001, K makes the
│          coded evidence `A -> not A` equivalent at the derivability
│          level to `not A` itself. This precision contract is
│          additive and does not change the shape of the legacy
│          aggregate witnesses.
│
*)

Definition CODED_RECOGNITION_REFUTATION_SPECIFICATION_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    CodedRecognitionAccepted M Gamma A <->
    regulator_theory_checked_derivable M Gamma
      (formula_negation A).

(*
│
│          The regulated-assumption contract packages every `AsIF`
│          formula as explicitly assumption-licensed content.
│
*)

Definition REGULATED_ASSUMPTION_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    AsIF M Gamma A ->
    AssumptionLicensedContent M Gamma A.

Definition CODED_RECURSIVE_MIRROR_CONTRACT : Prop :=
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

Definition LOCAL_CODED_RECURSIVE_MIRROR_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    RecursiveMirrorLocallyConsistent M Gamma mirror_step chi ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth : nat,
      ~ CodedRecognitionAccepted M Gamma
          (recursive_mirror_formula depth mirror_step chi).

Definition CODED_SEED_RECURSIVE_MIRROR_CONTRACT : Prop :=
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

(*
│
│          The externalization contract transports fixed-point
│          irrefutability through an explicit system response
│          relation.
│
*)

Definition CONDITIONAL_EXTERNALIZATION_CONTRACT : Prop :=
  forall (System : Type)
         (system : System)
         (externalizes : ExternalizationRelation System)
         (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalizationResponse
      System M Gamma externalizes system ->
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    externalizes system chi.

(*
│
│          The attribution contract transports fixed-point
│          irrefutability through an explicit internal-or-external
│          provenance response.
│
*)

Definition CONDITIONAL_ATTRIBUTION_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (internal_attribution external_attribution : AttributionCoding)
         (chi : Formula),
    AttributionResponse
      M Gamma internal_attribution external_attribution ->
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AsIF M Gamma (internal_attribution chi) \/
    AsIF M Gamma (external_attribution chi).

(*
│
│          The finite-operation contract certifies recurrence for
│          every total trace over a finite state carrier.
│
*)

Definition FINITE_OPERATIONAL_RECURRENCE_CONTRACT : Prop :=
  forall (State : Type)
         (F : FiniteOperationalLayer State),
    exists earlier later : nat,
      earlier < later /\
      later <= length (finite_operational_states F) /\
      operational_state_at F earlier =
      operational_state_at F later.

Definition LOGICAL_OPERATIONAL_RECURRENCE_CONTRACT : Prop :=
  forall (State : Type)
         (M : RegulatorTheory)
         (Gamma : Context)
         (L : LogicalOperationalLayer State M Gamma),
    exists earlier later : nat,
      earlier < later /\
      later <= length
        (finite_operational_states (logical_finite_operation L)) /\
      operational_state_at (logical_finite_operation L) earlier =
        operational_state_at (logical_finite_operation L) later /\
      operational_state_at (logical_finite_operation L) (S earlier) =
        operational_state_at (logical_finite_operation L) (S later) /\
      logical_operational_content L
          (operational_state_at (logical_finite_operation L) earlier) =
        logical_operational_content L
          (operational_state_at (logical_finite_operation L) later) /\
      AsIF M Gamma
        (logical_operational_content L
           (operational_state_at (logical_finite_operation L) earlier)) /\
      ~ CodedRecognitionAccepted M Gamma
          (logical_operational_content L
             (operational_state_at
                (logical_finite_operation L) earlier)).

Definition ATTRIBUTED_PROVENANCE_OPERATIONAL_RECURRENCE_CONTRACT : Prop :=
  forall State M Gamma
         (L : AttributedProvenanceOperationalLayer State M Gamma),
    exists earlier later,
      earlier < later /\
      operational_state_at
          (logical_finite_operation (attributed_provenance_logical_operation L)) earlier =
        operational_state_at
          (logical_finite_operation (attributed_provenance_logical_operation L)) later /\
      operational_attribution_observation L earlier =
        operational_attribution_observation L later /\
      AsIF M Gamma
        (logical_operational_content (attributed_provenance_logical_operation L)
           (operational_state_at
              (logical_finite_operation
                 (attributed_provenance_logical_operation L)) earlier)) /\
      ~ CodedRecognitionAccepted M Gamma
          (logical_operational_content (attributed_provenance_logical_operation L)
             (operational_state_at
                (logical_finite_operation
                   (attributed_provenance_logical_operation L)) earlier)).

Definition CONCRETE_EXTERNALIZATION_CONTRACT : Prop :=
  forall State M Gamma
         (L : AttributedProvenanceOperationalLayer State M Gamma)
         time,
    operational_state_attributed_provenance L
      (operational_state_at
         (logical_finite_operation
            (attributed_provenance_logical_operation L)) time) =
      provenance_external ->
    operational_externalizes L
      (operational_state_at
         (logical_finite_operation
            (attributed_provenance_logical_operation L)) time)
      (logical_operational_content
         (attributed_provenance_logical_operation L)
         (operational_state_at
            (logical_finite_operation
               (attributed_provenance_logical_operation L)) time)).

(*
│
│          The principles contract collects the literal certified and
│          conditional conclusions supported by Symbolic Regulation.
│
*)

Definition PRINCIPLES_OF_SYMBOLIC_REGULATION_CONTRACT : Prop :=
  (forall (M : RegulatorTheory)
          (Gamma : Context)
          (chi : Formula),
      ExternalMirrorPosition M Gamma chi ->
      MirrorConsistent M Gamma ->
      ~ CodedRecognitionAccepted M Gamma chi) /\
  (forall (M : RegulatorTheory)
          (Gamma : Context)
          (mirror_step : Formula -> Formula)
          (chi : Formula),
      RecursiveMirrorAdequacy M Gamma mirror_step chi ->
      MirrorConsistent M Gamma ->
      forall depth : nat,
        AsIF M Gamma
          (recursive_mirror_formula depth mirror_step chi) /\
        ~ CodedRecognitionAccepted M Gamma
            (recursive_mirror_formula depth mirror_step chi)) /\
  CONCRETE_EXTERNALIZATION_CONTRACT.

(*
│
│          Optional specification bundling relative consistency,
│          witnessed mirror questions, and response traces. The
│          unbounded conclusion retains its outcome-decidability
│          premise.
│
*)

Record CONTROL_QUESTION_SPECIFICATION_CONTRACT : Prop := {
  certified_world_brain_model_consistency :
    forall (V : EpistemicWorld)
           (brain model : RegulatorTheory)
           (Gamma : Context)
           (frame : WorldBrainModelFrame V brain model Gamma),
      MirrorConsistent model Gamma;

  certified_control_negative_answer_impossible :
    forall (M : RegulatorTheory)
           (Gamma : Context)
           (question : ControlQuestion M Gamma),
      MirrorConsistent M Gamma ->
      ~ ControlAnswersNo M Gamma question;

  certified_binary_control_forces_yes :
    forall (M : RegulatorTheory)
           (Gamma : Context)
           (question : ControlQuestion M Gamma),
      MirrorConsistent M Gamma ->
      BinaryControlDecision M Gamma question ->
      ControlAnswersYes M Gamma question;

  certified_world_sound_binary_control_conflict :
    forall (V : EpistemicWorld)
           (brain model : RegulatorTheory)
           (Gamma : Context)
           (frame : WorldBrainModelFrame V brain model Gamma)
           (question : ControlQuestion model Gamma),
      WorldFormulaConsistent V ->
      TheorySoundInWorld V model Gamma ->
      WorldRefutesControlClaim V question ->
      ~ BinaryControlDecision model Gamma question;

  certified_finite_yes_or_recursive_reentry :
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
        ReentersThrough process fuel;

  certified_yes_or_recursive_reentry :
    forall (M : RegulatorTheory)
           (Gamma : Context)
           (mirror_step : Formula -> Formula)
           (chi : Formula)
           (process : RecursiveControlProcess M Gamma mirror_step chi),
      RecursiveMirrorAdequacy M Gamma mirror_step chi ->
      MirrorConsistent M Gamma ->
      ControlOutcomeDecidable process ->
      EventuallyAnswersYes process \/
      ReentersForever process
}.

(*
│
│          The compact Mirror endpoint bundles full-fixed-point
│          collapse, live mirror irrefutability, and coded recognition
│          opacity.
│
*)

Definition MIRROR_LEMMA_CONTRACT : Prop :=
  FULL_FIXED_POINT_COLLAPSE_CONTRACT /\
  ASIF_FROM_EXTERNAL_MIRROR_POSITION_CONTRACT /\
  CHECKED_REFUTATION_RECOGNITION_OPACITY_CONTRACT /\
  CODED_RECOGNITION_OPACITY_CONTRACT /\
  CODED_RECOGNITION_EVIDENCE_SPECIFICATION_CONTRACT.

(*
│
│          The compact recursive endpoint bundles all-depth mirror
│          adequacy with the seed-plus-preservation construction.
│
*)

Definition RECURSIVE_MIRROR_LEMMA_CONTRACT : Prop :=
  CODED_RECURSIVE_MIRROR_CONTRACT /\
  CODED_SEED_RECURSIVE_MIRROR_CONTRACT.

(*
│
│          Primary theorem-core contract. Optional attribution,
│          provenance, externalization, and response specifications
│          are deliberately excluded.
│
*)

Definition L002_CORE_CONTRACT : Prop :=
  GOAL_FRAME_EXTERNAL_FIXED_POINT_CONTRACT /\
  FULL_FIXED_POINT_COLLAPSE_CONTRACT /\
  LOCAL_MIRROR_IRREFUTABILITY_CONTRACT /\
  LOCAL_CODED_RECOGNITION_OPACITY_CONTRACT /\
  CODED_RECOGNITION_EVIDENCE_SPECIFICATION_CONTRACT /\
  LOCAL_CODED_RECURSIVE_MIRROR_CONTRACT.

Definition CORE_WITNESS : Prop :=
  L002_CORE_CONTRACT.

(*
│
│          Legacy broad contract over global mirror results and
│          optional operational and response-law surfaces.
│
*)

Definition SYMBOLIC_REGULATION_CONTRACT : Prop :=
  ASIF_FROM_EXTERNAL_MIRROR_POSITION_CONTRACT /\
  FULL_FIXED_POINT_COLLAPSE_CONTRACT /\
  CHECKED_REFUTATION_RECOGNITION_OPACITY_CONTRACT /\
  CODED_RECOGNITION_OPACITY_CONTRACT /\
  CODED_RECOGNITION_EVIDENCE_SPECIFICATION_CONTRACT /\
  REGULATED_ASSUMPTION_CONTRACT /\
  CODED_RECURSIVE_MIRROR_CONTRACT /\
  CODED_SEED_RECURSIVE_MIRROR_CONTRACT /\
  FINITE_OPERATIONAL_RECURRENCE_CONTRACT /\
  LOGICAL_OPERATIONAL_RECURRENCE_CONTRACT /\
  ATTRIBUTED_PROVENANCE_OPERATIONAL_RECURRENCE_CONTRACT /\
  CONCRETE_EXTERNALIZATION_CONTRACT /\
  CONDITIONAL_ATTRIBUTION_CONTRACT /\
  PRINCIPLES_OF_SYMBOLIC_REGULATION_CONTRACT /\
  CONDITIONAL_EXTERNALIZATION_CONTRACT /\
  CONTROL_QUESTION_SPECIFICATION_CONTRACT.

(*
│
│          Compatibility alias for the legacy broad contract. New
│          clients should prefer `CORE_WITNESS` for the theorem core.
│
*)

Definition WITNESS : Prop :=
  SYMBOLIC_REGULATION_CONTRACT.
