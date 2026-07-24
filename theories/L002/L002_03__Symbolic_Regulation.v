(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Optional consequence layer: finite-state recurrence plus conditional attribution, provenance, and externalization transports. The coded mirror theorems remain the L002 core.]]@*)

(*@head.end@*)

From L002 Require Export L002_02__Recursive_Mirror_Lemma.
From Stdlib Require Import Lia.

(*@section@[[FINITE OPERATIONAL LAYER]]@*)

(*@inline@[[A finite list with a duplicate has equal entries at two strictly ordered positions.]]@*)

Lemma finite_list_duplicate_positions :
  forall (A : Type)
         (eq_dec : forall x y : A, {x = y} + {x <> y})
         (l : list A) (d : A),
    ~ NoDup l ->
    exists i j : nat,
      i < j /\
      j < length l /\
      nth i l d = nth j l d.
Proof.
  intros A eq_dec l.
  induction l as [|a l IH]; intros d Hduplicate.
  - exfalso.
    apply Hduplicate.
    constructor.
  - destruct (in_dec eq_dec a l) as [Hin | Hnotin].
    + destruct (In_nth l a d Hin) as [position [Hbound Hequal]].
      exists O, (S position).
      simpl.
      repeat split; try lia.
      symmetry.
      exact Hequal.
    + assert (Htail : ~ NoDup l).
      {
        intro Hnodup.
        apply Hduplicate.
        constructor; assumption.
      }
      destruct (IH d Htail)
        as [earlier [later [Hlt [Hbound Hequal]]]].
      exists (S earlier), (S later).
      simpl.
      repeat split; try lia.
      exact Hequal.
Qed.

(*@inline@[[A total trace over a finite state carrier repeats a state among its first `N + 1` observations, where `N` is the carrier-list length.]]@*)

Theorem finite_operational_recurrence :
  forall (State : Type)
         (F : FiniteOperationalLayer State),
    exists earlier later : nat,
      earlier < later /\
      later <= length (finite_operational_states F) /\
      operational_state_at F earlier =
      operational_state_at F later.
Proof.
  intros State F.
  set (states := finite_operational_states F).
  set (trace :=
    map (operational_state_at F)
      (seq O (S (length states)))).
  assert (Hincl : incl trace states).
  {
    intros state Hin.
    unfold trace in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [time [Hequal _Hin]].
    subst state.
    exact (operational_state_enumerated F time).
  }
  assert (Hduplicate : ~ NoDup trace).
  {
    intro Hnodup.
    pose proof
      (NoDup_incl_length Hnodup Hincl) as Hlength.
    unfold trace in Hlength.
    rewrite length_map, length_seq in Hlength.
    lia.
  }
  destruct
    (finite_list_duplicate_positions
       State (operational_state_eq_dec F)
       trace (operational_state_at F O) Hduplicate)
    as [earlier [later [Hlt [Hbound Hequal]]]].
  exists earlier, later.
  split.
  - exact Hlt.
  - split.
    + unfold trace in Hbound.
      rewrite length_map, length_seq in Hbound.
      lia.
    + unfold trace in Hequal.
      assert (Hlater : later < S (length states)).
      {
        unfold trace in Hbound.
        rewrite length_map, length_seq in Hbound.
        exact Hbound.
      }
      assert (Hearlier : earlier < S (length states)) by lia.
      rewrite !map_nth in Hequal.
      rewrite
        (seq_nth (len := S (length states))
           O (n := earlier) O Hearlier) in Hequal.
      rewrite
        (seq_nth (len := S (length states))
           O (n := later) O Hlater) in Hequal.
      simpl in Hequal.
      exact Hequal.
Qed.

(*@section@[[LOGICAL OPERATIONAL REGULATION]]@*)

(*@inline@[[Finite recurrence in a logical operational layer repeats both the operational state and its associated formula, while retaining `AsIF` and recognition opacity at the repeated observation.]]@*)

Theorem logical_operational_recurrence :
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
Proof.
  intros State M Gamma L.
  destruct
    (finite_operational_recurrence
       State (logical_finite_operation L))
    as [earlier [later [Hlt [Hbound Hstate]]]].
  exists earlier, later.
  repeat split.
  - exact Hlt.
  - exact Hbound.
  - exact Hstate.
  - rewrite !logical_operational_trace_successor.
    now rewrite Hstate.
  - now rewrite Hstate.
  - exact (logical_operational_content_asif L earlier).
  - exact (logical_operational_content_opaque L earlier).
Qed.

(*@inline@[[Legacy structural attribution example: implication reflection is named as one branch and identity as the other. These are stipulated formula codings and demonstrate transport only; they do not identify real internal or external causal origin. The explicit `AttributedProvenanceOperationalLayer` below is the preferred operational attribution model, subject to the same origin guardrail.]]@*)

Definition implication_reflection_internal_attribution :
    AttributionCoding :=
  implication_reflection_mirror.

Definition unchanged_external_attribution : AttributionCoding :=
  fun A => A.

Theorem asif_implication_reflection_mirror :
  forall (M : RegulatorTheory) (Gamma : Context) (A : Formula),
    AsIF M Gamma A ->
    AsIF M Gamma (implication_reflection_mirror A).
Proof.
  intros M Gamma A Hasif Hnegmirror.
  apply Hasif.
  apply assumption_discharge.
  apply regulator_theory_checked_derivable_mp_lemma
    with (A := implication_reflection_mirror A).
  - apply checked_derivable_under_assumption.
    exact Hnegmirror.
  - apply regulator_theory_checked_derivable_mp_lemma with (A := A).
    + apply checked_derivable_under_assumption.
      exact (implication_reflection_mirror_intro M Gamma A).
    + exact (assumption_intro M Gamma A).
Qed.

(*@inline@[[The structural selected response always realizes the internal branch through implication-reflection preservation. Its selection premise is intentionally unused; it is retained as a compatibility/surface-inhabitation result, not evidence of attribution behavior.]]@*)

Theorem implication_reflection_selected_attribution_response :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (active : ActiveSchemaSet),
    SelectedAttributionResponse
      M Gamma active
      implication_reflection_internal_attribution
      unchanged_external_attribution.
Proof.
  intros M Gamma active A _Hselected Hasif.
  left.
  exact (asif_implication_reflection_mirror M Gamma A Hasif).
Qed.

(*@inline@[[At the recurrent observation, a selected operational layer yields a concrete internal-or-external attribution position through its registered response law.]]@*)

Theorem selected_operational_attribution_recurrence :
  forall (State : Type)
         (M : RegulatorTheory)
         (Gamma : Context)
         (internal_attribution external_attribution : AttributionCoding)
         (L : SelectedOperationalAttributionLayer
                State M Gamma
                internal_attribution external_attribution),
    exists earlier later : nat,
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
  intros State M Gamma internal_attribution external_attribution L.
  destruct
    (finite_operational_recurrence
       State
       (logical_finite_operation (selected_logical_operation L)))
    as [earlier [later [Hlt [_Hbound Hstate]]]].
  exists earlier, later.
  repeat split.
  - exact Hlt.
  - exact Hstate.
  - apply (selected_operational_attribution_response L).
    + exact (selected_operational_content_selected L earlier).
    + exact
        (logical_operational_content_asif
           (selected_logical_operation L) earlier).
Qed.

(*@section@[[OPERATIONAL PROVENANCE OBSERVATIONS]]@*)

Definition operational_attribution_observation
    {State M Gamma}
    (L : AttributedProvenanceOperationalLayer State M Gamma)
    (time : nat) : CodedAttributionObservation :=
  let state :=
    operational_state_at
      (logical_finite_operation (attributed_provenance_logical_operation L)) time in
  observes_provenance
    (logical_operational_content
       (attributed_provenance_logical_operation L) state)
    (operational_state_attributed_provenance L state).

Theorem operational_attribution_is_concrete :
  forall State M Gamma
         (L : AttributedProvenanceOperationalLayer State M Gamma)
         time,
    (exists A,
       operational_attribution_observation L time =
       observes_provenance A provenance_internal) \/
    (exists A,
       operational_attribution_observation L time =
       observes_provenance A provenance_external).
Proof.
  intros State M Gamma L time.
  unfold operational_attribution_observation.
  destruct
    (operational_state_attributed_provenance L
       (operational_state_at
          (logical_finite_operation
             (attributed_provenance_logical_operation L)) time)).
  - left. eexists. reflexivity.
  - right. eexists. reflexivity.
Qed.

(*@inline@[[Finite recurrence repeats the complete provenance observation because both logical content and provenance are functions of the repeated operational state.]]@*)

Theorem attributed_provenance_operational_recurrence :
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
Proof.
  intros State M Gamma L.
  destruct
    (logical_operational_recurrence
       State M Gamma (attributed_provenance_logical_operation L))
    as [earlier [later
      [Hlt [_Hbound [Hstate [_Hnext [Hcontent [Hasif Hopaque]]]]]]]].
  exists earlier, later.
  repeat split.
  - exact Hlt.
  - exact Hstate.
  - unfold operational_attribution_observation.
    now rewrite Hstate.
  - exact Hasif.
  - exact Hopaque.
Qed.

(*@section@[[OBSERVABLE EXTERNALIZATION]]@*)

(*@inline@[[Concrete operational externalization is an observed state whose explicit provenance tag is external and whose logical content is the advertised formula.]]@*)

Definition operational_externalizes
    {State M Gamma}
    (L : AttributedProvenanceOperationalLayer State M Gamma)
    : ExternalizationRelation State :=
  fun state A =>
    operational_state_attributed_provenance L state = provenance_external /\
    logical_operational_content
      (attributed_provenance_logical_operation L) state = A.

Theorem externally_attributed_observation_externalizes :
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
  intros State M Gamma L time Hexternal.
  split.
  - exact Hexternal.
  - reflexivity.
Qed.

(*@inline@[[A one-way external mirror position is internally non-refutable in every consistent embedded theory.]]@*)

Theorem oracle_irrefutability_principle :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AsIF M Gamma chi.
Proof.
  exact external_mirror_position_forces_asif.
Qed.

(*@inline@[[A fixed symbolic regulator cannot adequately recognize a one-way mirror position from inside its regulated position.]]@*)

Theorem recognition_opacity_principle :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    ~ InternalFixedPointRecognition
        M Gamma (fixed_recognition_claim S) chi.
Proof.
  intros Slambda M Gamma S chi Hfixed.
  exact
    (proj2
       (fixed_regulator_mirror_opacity
          Slambda M Gamma S chi Hfixed)).
Qed.

(*@inline@[[A supplied attribution response transports fixed-point irrefutability to an internal-or-external provenance position.]]@*)

Theorem conditional_attribution_principle :
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
Proof.
  intros M Gamma internal_attribution external_attribution chi
    Hresponse Hfixed Hconsistent.
  apply Hresponse.
  exact
    (oracle_irrefutability_principle
       M Gamma chi Hfixed Hconsistent).
Qed.

(*@inline@[[A selected attribution response transports fixed-point irrefutability only when the fixed point belongs to the finite active schema set.]]@*)

Theorem selected_conditional_attribution_principle :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (active : ActiveSchemaSet)
         (internal_attribution external_attribution : AttributionCoding)
         (chi : Formula),
    SelectedAttributionResponse
      M Gamma active internal_attribution external_attribution ->
    SchemaSelected active chi ->
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AsIF M Gamma (internal_attribution chi) \/
    AsIF M Gamma (external_attribution chi).
Proof.
  intros M Gamma active internal_attribution external_attribution chi
    Hresponse Hselected Hfixed Hconsistent.
  apply Hresponse.
  - exact Hselected.
  - exact
      (oracle_irrefutability_principle
         M Gamma chi Hfixed Hconsistent).
Qed.

(*@section@[[ATTRIBUTIONAL STANDOFF]]@*)

(*@inline@[[Exported attributional-standoff result. A supplied ambiguity response makes both provenance formulas irrefutable at the mirror position. The conclusion is `AttributionallyAmbiguous`, not a selection of or evidential lean toward either attribution. This theorem is exported by the API but is not a conjunct of the certified `WITNESS`.]]@*)

Theorem conditional_attributional_ambiguity_principle :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (internal_attribution external_attribution : AttributionCoding)
         (chi : Formula),
    AttributionalAmbiguityResponse
      M Gamma internal_attribution external_attribution ->
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AttributionallyAmbiguous
      M Gamma internal_attribution external_attribution chi.
Proof.
  intros M Gamma internal_attribution external_attribution chi
    Hresponse Hfixed Hconsistent.
  apply Hresponse.
  exact
    (oracle_irrefutability_principle
       M Gamma chi Hfixed Hconsistent).
Qed.

(*@section@[[ONE-SIDED RESPONSE BRIDGES]]@*)

(*@inline@[[Under an opacity response, a fixed-point position whose supplied recognition process is opaque leaves its external-attribution formula irrefutable. This one-sided conclusion comes from the explicit response premise, not from opacity by itself.]]@*)

Theorem conditional_opaque_external_attribution_principle :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (external_attribution : AttributionCoding)
         (chi : Formula),
    OpacityExternalAttributionResponse
      M Gamma (fixed_recognition_claim S) external_attribution ->
    ExternalMirrorPosition M Gamma chi ->
    AsIF M Gamma (external_attribution chi).
Proof.
  intros Slambda M Gamma S external_attribution chi
    Hresponse Hfixed.
  apply Hresponse.
  - exact
      (proj1
         (proj1
            (fixed_regulator_mirror_opacity
               Slambda M Gamma S chi Hfixed))).
  - exact
      (recognition_opacity_principle
         Slambda M Gamma S chi Hfixed).
Qed.

(*@inline@[[A supplied externalization response transports fixed-point irrefutability to external attribution for the selected system.]]@*)

Theorem conditional_externalization_principle :
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
Proof.
  intros System system externalizes M Gamma chi
    Hresponse Hfixed Hconsistent.
  apply Hresponse.
  exact
    (oracle_irrefutability_principle
       M Gamma chi Hfixed Hconsistent).
Qed.

(*@inline@[[The same response law externalizes every finite iterate of an adequate recursive mirror.]]@*)

Theorem recursive_conditional_externalization_principle :
  forall (System : Type)
         (system : System)
         (externalizes : ExternalizationRelation System)
         (M : RegulatorTheory)
         (Gamma : Context)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    ExternalizationResponse
      System M Gamma externalizes system ->
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    MirrorConsistent M Gamma ->
    forall depth : nat,
      externalizes system
        (recursive_mirror_formula depth mirror_step chi).
Proof.
  intros System system externalizes M Gamma mirror_step chi
    Hresponse Hadequate Hconsistent depth.
  apply Hresponse.
  exact
    (recursive_mirror_irrefutability
       M Gamma mirror_step chi Hadequate Hconsistent depth).
Qed.

(*@section@[[PRINCIPLES OF SYMBOLIC REGULATION]]@*)

(*@inline@[[Concrete coded fixed-point opacity excludes acceptance by L002's finite recognition-certificate regulator.]]@*)

Theorem coded_fixed_point_certificate_opacity :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    ~ CodedRecognitionAccepted M Gamma chi.
Proof.
  exact coded_recognition_opacity.
Qed.

(*@section@[[LEGACY INTERPRETIVE ALIASES]]@*)

(*@inline@[[Compatibility wrapper for the legacy `InternalFixedPointRecognition` interface.]]@*)

Theorem fixed_point_certificate_opacity :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    ~ InternalFixedPointRecognition
        M Gamma (fixed_recognition_claim S) chi.
Proof.
  exact recognition_opacity_principle.
Qed.

(*@inline@[[Legacy name for `fixed_point_certificate_opacity`; no broader conclusion is added.]]@*)

Theorem incomprehensibility_of_symbolic_regulation :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    ~ InternalFixedPointRecognition
        M Gamma (fixed_recognition_claim S) chi.
Proof.
  exact fixed_point_certificate_opacity.
Qed.

(*@inline@[[Legacy name for all-finite-depth `AsIF` plus legacy recognition opacity.]]@*)

Theorem finite_perpetuity_of_ignorance :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (mirror_step : Formula -> Formula)
         (chi : Formula),
    RecursiveMirrorAdequacy M Gamma mirror_step chi ->
    forall depth : nat,
      AsIF M Gamma
        (recursive_mirror_formula depth mirror_step chi) /\
      ~ InternalFixedPointRecognition
          M Gamma
          (fixed_recognition_claim S)
          (recursive_mirror_formula depth mirror_step chi).
Proof.
  intros Slambda M Gamma S mirror_step chi Hadequate.
  destruct
    (recursive_mirror_lemma
       Slambda M Gamma S mirror_step chi Hadequate)
    as [Hposition Hopacity].
  intro depth.
  split.
  - exact (Hposition depth).
  - exact (Hopacity depth).
Qed.

(*@inline@[[Legacy name for conditional external-attribution transport through `OpacityExternalAttributionResponse`.]]@*)

Theorem paradox_of_the_external :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (external_attribution : AttributionCoding)
         (chi : Formula),
    OpacityExternalAttributionResponse
      M Gamma (fixed_recognition_claim S) external_attribution ->
    ExternalMirrorPosition M Gamma chi ->
    AsIF M Gamma (external_attribution chi).
Proof.
  exact conditional_opaque_external_attribution_principle.
Qed.
