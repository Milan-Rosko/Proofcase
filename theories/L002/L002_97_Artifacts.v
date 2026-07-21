(*L002_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / L002_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Artifact layer for L002/SYMBOLIC REGULATION. We certify the public
  contracts, assemble the package witness, and redirect assumption reports
  for the citation theorems and terminal endpoint.

*)

From L002 Require Export L002_95_API.

(*
│
│          Certification endpoint for fixed-point irrefutability.
│
*)

Theorem certified_asif_from_external_mirror_position_contract :
  ASIF_FROM_EXTERNAL_MIRROR_POSITION_CONTRACT.
Proof.
  exact external_mirror_position_forces_asif.
Qed.

Theorem certified_full_fixed_point_collapse_contract :
  FULL_FIXED_POINT_COLLAPSE_CONTRACT.
Proof.
  exact external_fixed_point_unconditionally_collapses.
Qed.

(*
│
│          Certification endpoint for concrete checked
│          refutation-recognition opacity.
│
*)

Theorem certified_checked_refutation_recognition_opacity_contract :
  CHECKED_REFUTATION_RECOGNITION_OPACITY_CONTRACT.
Proof.
  exact external_mirror_position_excludes_checked_refutation_recognition.
Qed.

(*
│
│          Certification endpoint for the first-class coded
│          recognition regulator.
│
*)

Theorem certified_coded_recognition_opacity_contract :
  CODED_RECOGNITION_OPACITY_CONTRACT.
Proof.
  exact coded_recognition_acceptance_excluded.
Qed.

Theorem certified_coded_recognition_evidence_specification_contract :
  CODED_RECOGNITION_EVIDENCE_SPECIFICATION_CONTRACT.
Proof.
  exact coded_recognition_acceptance_iff_evidence.
Qed.

(*
│
│          Certification endpoint for regulated assumptions.
│
*)

Theorem certified_regulated_assumption_contract :
  REGULATED_ASSUMPTION_CONTRACT.
Proof.
  exact licensed_assumption_forces_content.
Qed.

(*
│
│          Certification endpoint for the Recursive Mirror Lemma.
│
*)

Theorem certified_coded_recursive_mirror_contract :
  CODED_RECURSIVE_MIRROR_CONTRACT.
Proof.
  exact coded_recursive_mirror_lemma.
Qed.

Theorem certified_coded_seed_recursive_mirror_contract :
  CODED_SEED_RECURSIVE_MIRROR_CONTRACT.
Proof.
  exact coded_recursive_mirror_lemma_from_seed.
Qed.

(*
│
│          Certification endpoint for finite operational recurrence.
│
*)

Theorem certified_finite_operational_recurrence_contract :
  FINITE_OPERATIONAL_RECURRENCE_CONTRACT.
Proof.
  exact finite_operational_recurrence.
Qed.

Theorem certified_logical_operational_recurrence_contract :
  LOGICAL_OPERATIONAL_RECURRENCE_CONTRACT.
Proof.
  exact logical_operational_recurrence.
Qed.

Theorem certified_attributed_provenance_operational_recurrence_contract :
  ATTRIBUTED_PROVENANCE_OPERATIONAL_RECURRENCE_CONTRACT.
Proof.
  exact attributed_provenance_operational_recurrence.
Qed.

Theorem certified_concrete_externalization_contract :
  CONCRETE_EXTERNALIZATION_CONTRACT.
Proof.
  exact externally_attributed_observation_externalizes.
Qed.

(*
│
│          Certification endpoint for conditional attribution.
│
*)

Theorem certified_conditional_attribution_contract :
  CONDITIONAL_ATTRIBUTION_CONTRACT.
Proof.
  exact conditional_attribution_principle.
Qed.

(*
│
│          Certification endpoint for the realizable Principles of
│          Symbolic Regulation.
│
*)

Theorem certified_principles_of_symbolic_regulation_contract :
  PRINCIPLES_OF_SYMBOLIC_REGULATION_CONTRACT.
Proof.
  unfold PRINCIPLES_OF_SYMBOLIC_REGULATION_CONTRACT.
  split.
  - exact coded_fixed_point_certificate_opacity.
  - split.
    + intros M Gamma mirror_step chi Hadequate Hconsistent depth.
      destruct
        (coded_recursive_mirror_lemma
           M Gamma mirror_step chi Hadequate Hconsistent)
        as [Hasif Hopaque].
      split.
      * exact (Hasif depth).
      * exact (Hopaque depth).
    + exact certified_concrete_externalization_contract.
Qed.

(*
│
│          Certification endpoint for conditional externalization.
│
*)

Theorem certified_conditional_externalization_contract :
  CONDITIONAL_EXTERNALIZATION_CONTRACT.
Proof.
  exact conditional_externalization_principle.
Qed.

(*
│
│          Certification endpoint for the world, brain, embedded
│          model, witnessed control question, and recursive response
│          specification.
│
*)

Theorem certified_control_question_specification_contract :
  CONTROL_QUESTION_SPECIFICATION_CONTRACT.
Proof.
  constructor.
  - exact world_brain_model_frame_model_consistent.
  - exact control_question_negative_answer_impossible.
  - exact control_question_binary_decision_forces_yes.
  - exact world_sound_binary_control_decision_impossible.
  - exact finite_yes_or_recursive_reentry.
  - exact yes_or_recursive_reentry.
Qed.

(*
│
│          The certified package contract is the conjunction of the
│          subordinate endpoints.
│
*)

Theorem certified_symbolic_regulation_contract :
  SYMBOLIC_REGULATION_CONTRACT.
Proof.
  unfold SYMBOLIC_REGULATION_CONTRACT.
  split.
  - exact certified_asif_from_external_mirror_position_contract.
  - split.
    + exact certified_full_fixed_point_collapse_contract.
    + split.
      * exact certified_checked_refutation_recognition_opacity_contract.
      * split.
        -- exact certified_coded_recognition_opacity_contract.
        -- split.
           ++ exact certified_coded_recognition_evidence_specification_contract.
           ++ split.
              ** exact certified_regulated_assumption_contract.
              ** split.
                 --- exact certified_coded_recursive_mirror_contract.
                 --- split.
                     +++ exact certified_coded_seed_recursive_mirror_contract.
                     +++ split.
                         *** exact certified_finite_operational_recurrence_contract.
                         *** split.
                             ---- exact certified_logical_operational_recurrence_contract.
                             ---- split.
                                  ++++ exact certified_attributed_provenance_operational_recurrence_contract.
                                  ++++ split.
                                       ***** exact certified_concrete_externalization_contract.
                                       ***** split.
                                             ------ exact certified_conditional_attribution_contract.
                                             ------ split.
                                                    +++++++ exact certified_principles_of_symbolic_regulation_contract.
                                                    +++++++ split.
                                                            { exact certified_conditional_externalization_contract. }
                                                            { exact certified_control_question_specification_contract. }
Qed.

(*
│
│          `mirror_lemma_qed` is the compact terminal endpoint for
│          full-fixed-point collapse and live mirror opacity.
│
*)

Theorem mirror_lemma_qed :
  MIRROR_LEMMA_CONTRACT.
Proof.
  unfold MIRROR_LEMMA_CONTRACT.
  split.
  - exact certified_full_fixed_point_collapse_contract.
  - split.
    + exact certified_asif_from_external_mirror_position_contract.
    + split.
      * exact certified_checked_refutation_recognition_opacity_contract.
      * split.
        -- exact certified_coded_recognition_opacity_contract.
        -- exact certified_coded_recognition_evidence_specification_contract.
Qed.

(*
│
│          `recursive_mirror_lemma_qed` is the compact terminal
│          endpoint for recursive mirror opacity.
│
*)

Theorem recursive_mirror_lemma_qed :
  RECURSIVE_MIRROR_LEMMA_CONTRACT.
Proof.
  split.
  - exact certified_coded_recursive_mirror_contract.
  - exact certified_coded_seed_recursive_mirror_contract.
Qed.

(*
│
│          `symbolic_regulation_qed` is the terminal package witness
│          theorem.
│
*)

Theorem symbolic_regulation_qed :
  WITNESS.
Proof.
  exact certified_symbolic_regulation_contract.
Qed.

(*
│
│          Assumption reporting is intentionally compact: one endpoint
│          for Mirror, one for recursive Mirror, and one for the
│          complete Symbolic Regulation package.
│
*)

Redirect "theories/L002/_appendix/_assumptions/mirror_lemma_qed"
  Print Assumptions mirror_lemma_qed.

Redirect "theories/L002/_appendix/_assumptions/recursive_mirror_lemma_qed"
  Print Assumptions recursive_mirror_lemma_qed.

Redirect "theories/L002/_appendix/_assumptions/symbolic_regulation_qed"
  Print Assumptions symbolic_regulation_qed.
