(*L002_98_Sanity.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                          Proofcase / L002_98_Sanity                          │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Sanity layer for L002/SYMBOLIC REGULATION. We check concrete mirror
  iteration and restate the fixed-point, recursive-opacity, and
  conditional-externalization theorem shapes against the public artifact
  import.

*)

From L002 Require Import L002_97_Artifacts.

(*
│
│          The sanity seed is the closed implication `Bot -> Bot`.
│
*)

Definition sanity_chi : Formula :=
  Imp Bot Bot.

(*
│
│          The sanity mirror step maps `A` to the self-implication `A
│          -> A`.
│
*)

Definition sanity_mirror_step (A : Formula) : Formula :=
  Imp A A.

(*
│
│          The sanity operational layer alternates over a two-element
│          Boolean carrier.
│
*)

Definition sanity_finite_operation : FiniteOperationalLayer bool.
Proof.
  refine
    {| finite_operational_states := [true; false];
       operational_state_eq_dec := Bool.bool_dec;
       operational_state_at := Nat.even |}.
  intro time.
  destruct (Nat.even time); simpl; auto.
Defined.

Example sanity_finite_operation_repeats :
  exists earlier later,
    earlier < later /\
    later <= length
      (finite_operational_states sanity_finite_operation) /\
    operational_state_at sanity_finite_operation earlier =
    operational_state_at sanity_finite_operation later.
Proof.
  exact
    (finite_operational_recurrence
       bool sanity_finite_operation).
Qed.

(*
│
│          The logical recurrence API repeats a state and its formula
│          while retaining `AsIF` and recognition opacity.
│
*)

Example sanity_logical_operational_recurrence_shape :
  forall State M Gamma
         (L : LogicalOperationalLayer State M Gamma),
    exists earlier later,
      earlier < later /\
      operational_state_at (logical_finite_operation L) earlier =
        operational_state_at (logical_finite_operation L) later /\
      AsIF M Gamma
        (logical_operational_content L
           (operational_state_at (logical_finite_operation L) earlier)) /\
      ~ CodedRecognitionAccepted M Gamma
          (logical_operational_content L
             (operational_state_at (logical_finite_operation L) earlier)).
Proof.
  intros State M Gamma L.
  destruct (logical_operational_recurrence State M Gamma L)
    as [earlier [later
      [Hlt [_Hbound [Hstate [_Hnext [_Hformula [Hasif Hopaque]]]]]]]].
  exists earlier, later.
  repeat split; assumption.
Qed.

(*
│
│          The concrete implication-reflection coding supplies a
│          selected attribution response without an empirical response
│          hypothesis.
│
*)

Example sanity_concrete_selected_attribution_response :
  forall M Gamma active,
    SelectedAttributionResponse
      M Gamma active
      implication_reflection_internal_attribution
      unchanged_external_attribution.
Proof.
  exact implication_reflection_selected_attribution_response.
Qed.

(*
│
│          A selected operational layer yields attribution at a
│          recurrent logical observation.
│
*)

Example sanity_selected_operational_attribution_recurrence_shape :
  forall State M Gamma internal_attribution external_attribution
         (L : SelectedOperationalAttributionLayer
                State M Gamma
                internal_attribution external_attribution),
    exists earlier later,
      earlier < later /\
      operational_state_at
          (logical_finite_operation (selected_logical_operation L)) earlier =
        operational_state_at
          (logical_finite_operation (selected_logical_operation L)) later /\
      (AsIF M Gamma
         (internal_attribution
            (logical_operational_content (selected_logical_operation L)
               (operational_state_at
                  (logical_finite_operation
                     (selected_logical_operation L)) earlier))) \/
       AsIF M Gamma
         (external_attribution
            (logical_operational_content (selected_logical_operation L)
               (operational_state_at
                  (logical_finite_operation
                     (selected_logical_operation L)) earlier)))).
Proof.
  exact selected_operational_attribution_recurrence.
Qed.

Example sanity_attributed_provenance_operational_recurrence_shape :
  forall State M Gamma
         (L : AttributedProvenanceOperationalLayer State M Gamma),
    exists earlier later,
      earlier < later /\
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
Proof.
  intros State M Gamma L.
  destruct (attributed_provenance_operational_recurrence State M Gamma L)
    as [earlier [later [Hlt [_Hstate [Hobservation [Hasif Hopaque]]]]]].
  exists earlier, later.
  repeat split; assumption.
Qed.

Example sanity_externally_attributed_observation_externalizes_shape :
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
Proof.
  exact externally_attributed_observation_externalizes.
Qed.

(*
│
│          Zero mirror steps return the seed formula.
│
*)

Example sanity_mirror_zero :
  recursive_mirror_formula O sanity_mirror_step sanity_chi =
  sanity_chi.
Proof.
  reflexivity.
Qed.

(*
│
│          Two mirror steps produce the self-implication of the first
│          iterate.
│
*)

Example sanity_mirror_two :
  recursive_mirror_formula 2 sanity_mirror_step sanity_chi =
  Imp (Imp sanity_chi sanity_chi) (Imp sanity_chi sanity_chi).
Proof.
  reflexivity.
Qed.

(*
│
│          A full negation fixed point unconditionally collapses in
│          the M001 specialization.
│
*)

Example sanity_external_fixed_point_collapse_shape :
  forall M Gamma chi,
    ExternalFixedPoint M Gamma chi ->
    regulator_theory_checked_derivable M Gamma Bot.
Proof.
  exact external_fixed_point_unconditionally_collapses.
Qed.

Example sanity_full_fixed_point_incompatible_with_consistency :
  forall M Gamma chi,
    ExternalFixedPoint M Gamma chi ->
    MirrorConsistent M Gamma ->
    False.
Proof.
  exact external_fixed_point_incompatible_with_mirror_consistency.
Qed.

Example sanity_chi_is_external_mirror_position :
  forall M Gamma,
    ExternalMirrorPosition M Gamma sanity_chi.
Proof.
  intros M Gamma.
  apply checked_derivable_is_external_mirror_position.
  unfold sanity_chi.
  apply assumption_discharge.
  exact (assumption_intro M Gamma Bot).
Qed.

(*
│
│          The preferred public theorem uses the consistent one-way
│          mirror position.
│
*)

Example sanity_external_mirror_position_asif_shape :
  forall M Gamma chi,
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AsIF M Gamma chi.
Proof.
  exact external_mirror_position_forces_asif.
Qed.

(*
│
│          The world-to-brain soundness and brain-to-model inclusion
│          frame transports consistency to the embedded model.
│
*)

Example sanity_world_brain_model_consistency_shape :
  forall V brain model Gamma
         (frame : WorldBrainModelFrame V brain model Gamma),
    MirrorConsistent model Gamma.
Proof.
  exact world_brain_model_frame_model_consistent.
Qed.

Example sanity_control_no_answer_impossible_shape :
  forall M Gamma (question : ControlQuestion M Gamma),
    MirrorConsistent M Gamma ->
    ~ ControlAnswersNo M Gamma question.
Proof.
  exact control_question_no_answer_impossible.
Qed.

Example sanity_binary_control_forces_yes_shape :
  forall M Gamma (question : ControlQuestion M Gamma),
    MirrorConsistent M Gamma ->
    BinaryControlDecision M Gamma question ->
    ControlAnswersYes M Gamma question.
Proof.
  exact control_question_binary_decision_forces_yes.
Qed.

(*
│
│          A world-refuted control claim conflicts with binary
│          decision only when model-to-world soundness is supplied in
│          addition to relative consistency.
│
*)

Example sanity_world_sound_binary_control_conflict_shape :
  forall V brain model Gamma
         (frame : WorldBrainModelFrame V brain model Gamma)
         (question : ControlQuestion model Gamma),
    WorldFormulaConsistent V ->
    TheorySoundInWorld V model Gamma ->
    WorldRefutesControlClaim V question ->
    ~ BinaryControlDecision model Gamma question.
Proof.
  exact world_sound_binary_control_decision_impossible.
Qed.

(*
│
│          The concrete recognition claim for `A` is definitionally
│          its object-level negation.
│
*)

Example sanity_refutation_recognition_claim (A : Formula) :
  refutation_recognition_claim A = formula_negation A.
Proof.
  reflexivity.
Qed.

(*
│
│          A consistent external mirror position excludes a retained
│          finite proof certificate for the concrete
│          refutation-recognition claim.
│
*)

Example sanity_checked_refutation_recognition_opacity_shape :
  forall M Gamma chi,
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    CheckedRefutationRecognitionCertificate M Gamma chi ->
    False.
Proof.
  exact external_mirror_position_excludes_checked_refutation_recognition.
Qed.

(*
│
│          Acceptance by the coded recognition regulator has the
│          advertised checked re-entry behavior.
│
*)

Example sanity_coded_recognition_acceptance_sound_shape :
  forall M Gamma A,
    CodedRecognitionAccepted M Gamma A ->
    UnderAssumption M Gamma A (formula_negation A).
Proof.
  exact coded_recognition_acceptance_sound.
Qed.

Example sanity_coded_recognition_evidence_shape :
  forall M Gamma A,
    CodedRecognitionAccepted M Gamma A ->
    regulator_theory_checked_derivable M Gamma
      (Imp A (formula_negation A)).
Proof.
  exact coded_recognition_acceptance_evidence.
Qed.

Example sanity_coded_recognition_exact_specification :
  forall M Gamma A,
    CodedRecognitionAccepted M Gamma A <->
    regulator_theory_checked_derivable M Gamma
      (Imp A (formula_negation A)).
Proof.
  exact coded_recognition_acceptance_iff_evidence.
Qed.

Example sanity_recognition_completes_fixed_point_shape :
  forall M Gamma A,
    ExternalMirrorPosition M Gamma A ->
    CodedRecognitionAccepted M Gamma A ->
    ExternalFixedPoint M Gamma A.
Proof.
  exact coded_recognition_completes_external_fixed_point.
Qed.

(*
│
│          A consistent external mirror position is opaque to the
│          first-class coded recognition regulator.
│
*)

Example sanity_coded_recognition_opacity_shape :
  forall M Gamma chi,
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    ~ CodedRecognitionAccepted M Gamma chi.
Proof.
  exact coded_recognition_opacity.
Qed.

(*
│
│          The public recursive theorem yields depth-indexed `AsIF`
│          and recognition opacity.
│
*)

Example sanity_recursive_mirror_shape :
  forall Slambda M Gamma
         (S : FixedSymbolicRegulator Slambda M Gamma)
         mirror_step chi,
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth,
      ~ InternalFixedPointRecognition
          M Gamma
          (fixed_recognition_claim S)
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  exact recursive_mirror_lemma.
Qed.

Example sanity_coded_recursive_mirror_shape :
  forall M Gamma mirror_step chi,
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth,
      ~ CodedRecognitionAccepted M Gamma
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  exact coded_recursive_mirror_lemma.
Qed.

Example sanity_coded_recursive_mirror_from_seed_shape :
  forall M Gamma mirror_step chi,
    ExternalMirrorPosition M Gamma chi ->
    MirrorStepPreservesExternalMirrorPositions M Gamma mirror_step ->
    MirrorConsistent M Gamma ->
    RecursiveMirrorPosition M Gamma mirror_step chi /\
    forall depth,
      ~ CodedRecognitionAccepted M Gamma
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  exact coded_recursive_mirror_lemma_from_seed.
Qed.

(*
│
│          The constructive bounded control theorem yields a positive
│          response within the observation bound or re-entry at every
│          stage through that bound.
│
*)

Example sanity_finite_yes_or_recursive_reentry_shape :
  forall M Gamma mirror_step chi
         (process : RecursiveControlProcess M Gamma mirror_step chi),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    forall fuel,
      (exists depth,
         depth <= fuel /\
         ControlAnswersYesAt process depth) \/
      ReentersThrough process fuel.
Proof.
  exact finite_yes_or_recursive_reentry.
Qed.

(*
│
│          The unbounded control theorem exposes the additional
│          outcome-decidability premise needed for eventual `yes` or
│          perpetual finite-depth re-entry.
│
*)

Example sanity_yes_or_recursive_reentry_shape :
  forall M Gamma mirror_step chi
         (process : RecursiveControlProcess M Gamma mirror_step chi),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    ControlOutcomeDecidable process ->
    EventuallyAnswersYes process \/
    ReentersForever process.
Proof.
  exact yes_or_recursive_reentry.
Qed.

(*
│
│          The identity mirror preserves every external fixed point.
│
*)

Example sanity_identity_mirror_preserves_positions :
  forall M Gamma,
    MirrorStepPreservesExternalMirrorPositions M Gamma (fun A => A).
Proof.
  intros M Gamma A Hfixed.
  exact Hfixed.
Qed.

(*
│
│          The seed-based API derives all finite identity-mirror
│          positions from a single external fixed point.
│
*)

Example sanity_recursive_mirror_from_seed_shape :
  forall Slambda M Gamma
         (S : FixedSymbolicRegulator Slambda M Gamma)
         chi,
    ExternalMirrorPosition M Gamma chi ->
    RecursiveMirrorPosition M Gamma (fun A => A) chi /\
    forall depth,
      ~ InternalFixedPointRecognition
          M Gamma
          (fixed_recognition_claim S)
          (recursive_mirror_formula depth (fun A => A) chi).
Proof.
  intros Slambda M Gamma S chi Hseed.
  apply recursive_mirror_lemma_from_seed.
  - exact Hseed.
  - exact (sanity_identity_mirror_preserves_positions M Gamma).
Qed.

(*
│
│          The implication-reflection mirror is a concrete
│          non-identity constructor with a certified mirror-position
│          preservation law.
│
*)

Example sanity_implication_reflection_mirror_from_seed :
  forall Slambda M Gamma
         (S : FixedSymbolicRegulator Slambda M Gamma)
         chi,
    ExternalMirrorPosition M Gamma chi ->
    RecursiveMirrorPosition
      M Gamma implication_reflection_mirror chi /\
    forall depth,
      ~ InternalFixedPointRecognition
          M Gamma
          (fixed_recognition_claim S)
          (recursive_mirror_formula
             depth implication_reflection_mirror chi).
Proof.
  intros Slambda M Gamma S chi Hseed.
  apply recursive_mirror_lemma_from_seed.
  - exact Hseed.
  - exact
      (implication_reflection_mirror_preserves_external_mirror_positions
         M Gamma).
Qed.

(*
│
│          The single-step externalization theorem consumes an
│          explicit externalization response.
│
*)

Example sanity_externalization_shape :
  forall (System : Type)
         (system : System)
         externalizes M Gamma chi,
    ExternalizationResponse
      System M Gamma externalizes system ->
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    externalizes system chi.
Proof.
  exact conditional_externalization_principle.
Qed.

(*
│
│          The attribution theorem leaves the internal or external
│          provenance formula irrefutable under a supplied response
│          law.
│
*)

Example sanity_attribution_shape :
  forall M Gamma internal_attribution external_attribution chi,
    AttributionResponse
      M Gamma internal_attribution external_attribution ->
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AsIF M Gamma (internal_attribution chi) \/
    AsIF M Gamma (external_attribution chi).
Proof.
  exact conditional_attribution_principle.
Qed.

(*
│
│          The ambiguity theorem permits neither supplied provenance
│          formula to be internally refuted.
│
*)

Example sanity_attributional_ambiguity_shape :
  forall M Gamma internal_attribution external_attribution chi,
    AttributionalAmbiguityResponse
      M Gamma internal_attribution external_attribution ->
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AttributionallyAmbiguous
      M Gamma internal_attribution external_attribution chi.
Proof.
  exact conditional_attributional_ambiguity_principle.
Qed.

(*
│
│          The recursive externalization theorem applies the same
│          response at every adequate mirror depth.
│
*)

Example sanity_recursive_externalization_shape :
  forall (System : Type)
         (system : System)
         externalizes M Gamma mirror_step chi,
    ExternalizationResponse
      System M Gamma externalizes system ->
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    forall depth,
      externalizes system
        (recursive_mirror_formula depth mirror_step chi).
Proof.
  exact recursive_conditional_externalization_principle.
Qed.

(*
│
│          Finite perpetuity pairs irrefutability and recognition
│          opacity at each adequate recursive depth.
│
*)

Example sanity_finite_perpetuity_shape :
  forall Slambda M Gamma
         (S : FixedSymbolicRegulator Slambda M Gamma)
         mirror_step chi,
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    forall depth,
      AsIF M Gamma
        (recursive_mirror_formula depth mirror_step chi) /\
      ~ InternalFixedPointRecognition
          M Gamma
          (fixed_recognition_claim S)
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  exact finite_perpetuity_of_ignorance.
Qed.

(*
│
│          The paradox-of-the-external surface retains the empirical
│          opacity-response premise.
│
*)

Example sanity_paradox_of_external_shape :
  forall Slambda M Gamma
         (S : FixedSymbolicRegulator Slambda M Gamma)
         external_attribution chi,
    OpacityExternalAttributionResponse
      M Gamma (fixed_recognition_claim S) external_attribution ->
    ExternalMirrorPosition M Gamma chi ->
    AsIF M Gamma (external_attribution chi).
Proof.
  exact paradox_of_the_external.
Qed.
