(*L002_01__Mirror_Unrefutability.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / L002_01__Mirror_Unrefutability                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Mirror-irrefutability layer. A bottom goal frame produces a collapsing full
  fixed point; the live theorem instead combines a one-way mirror with local
  or global consistency. Coded recognition supplies the missing fixed-point
  direction.

*)

From L002 Require Export L002_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            EXTERNAL CONSTRUCTION                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The minimal L001 bottom goal frame constructs a full
│          external fixed point for M001 checked derivability.
│
*)

Theorem l001_goal_frame_constructs_external_fixed_point :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal
      (regulator_theory_checked_derivable M Gamma)
      Code ev Bot ->
    exists chi : Formula,
      ExternalFixedPoint M Gamma chi.
Proof.
  intros M Gamma Code ev Hgoal.
  exact
    (eval_bottom_negfixp
       (regulator_theory_checked_derivable M Gamma)
       Code ev Hgoal).
Qed.

(*
│
│          Compatibility corollary: a universal L001 frame supplies
│          the bottom goal frame.
│
*)

Theorem l001_constructs_external_fixed_point :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    exists chi : Formula,
      ExternalFixedPoint M Gamma chi.
Proof.
  intros M Gamma Code E.
  exact
    (l001_goal_frame_constructs_external_fixed_point
       M Gamma Code (ceval_apply E)
       (eval_full_to_eval_bottom
          (regulator_theory_checked_derivable M Gamma)
          Code E)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             RECOGNITION RE-ENTRY                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The concrete refutation-recognition coding is adequate at
│          every formula: accepting its claim under `A` already is a
│          checked derivation of `not A` in that context.
│
*)

Theorem refutation_recognition_adequacy :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    RecognitionAdequacy
      M Gamma refutation_recognition_claim A.
Proof.
  intros M Gamma A Hrecognition.
  exact Hrecognition.
Qed.

(*
│
│          An accepted adequate recognition certificate yields a
│          base-context derivation of `not chi` by contradiction under
│          `chi` followed by deduction.
│
*)

Theorem recognition_reenters_regulator :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (recognition_claim : FixedPointRecognitionCoding)
         (chi : Formula),
    RecognitionAdequacy M Gamma recognition_claim chi ->
    InternalFixedPointRecognition M Gamma recognition_claim chi ->
    regulator_theory_checked_derivable M Gamma
      (formula_negation chi).
Proof.
  intros M Gamma recognition_claim chi Hadequate
    [_Hasif Hrecognition].
  apply assumption_discharge.
  apply regulator_theory_checked_derivable_mp_lemma with (A := chi).
  - exact (Hadequate Hrecognition).
  - exact (assumption_intro M Gamma chi).
Qed.

(*
│
│          Adequacy alone excludes the legacy recognition package
│          because it already contains `AsIF`; no mirror or
│          consistency premise is needed for this compatibility
│          result.
│
*)

Theorem recognition_adequacy_excludes_legacy_internal_recognition :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (recognition_claim : FixedPointRecognitionCoding)
         (chi : Formula),
    RecognitionAdequacy M Gamma recognition_claim chi ->
    ~ InternalFixedPointRecognition M Gamma recognition_claim chi.
Proof.
  intros M Gamma recognition_claim chi Hadequate Hrecognition.
  apply (proj1 Hrecognition).
  exact
    (recognition_reenters_regulator
       M Gamma recognition_claim chi Hadequate Hrecognition).
Qed.

(*
│
│          Acceptance by the coded recognition regulator re-enters the
│          embedded theory as a base-context derivation of `not A`:
│          checker soundness supplies `not A` under `A`, the
│          assumption supplies `A`, and deduction discharges it.
│
*)

Theorem coded_recognition_reenters_regulator :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    CodedRecognitionAccepted M Gamma A ->
    regulator_theory_checked_derivable M Gamma
      (formula_negation A).
Proof.
  intros M Gamma A Haccepted.
  apply assumption_discharge.
  apply regulator_theory_checked_derivable_mp_lemma with (A := A).
  - exact (coded_recognition_acceptance_sound M Gamma A Haccepted).
  - exact (assumption_intro M Gamma A).
Qed.

(*
│
│          Accepted recognition evidence supplies the missing forward
│          direction; together with the one-way mirror it reconstructs
│          the full negation fixed point exactly.
│
*)

Theorem coded_recognition_completes_external_fixed_point :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    ExternalMirrorPosition M Gamma A ->
    CodedRecognitionAccepted M Gamma A ->
    ExternalFixedPoint M Gamma A.
Proof.
  intros M Gamma A Hmirror Haccepted.
  split.
  - exact (coded_recognition_acceptance_evidence M Gamma A Haccepted).
  - exact Hmirror.
Qed.

(*
│
│          A derivation of `not chi` at an external fixed point
│          reconstructs `chi` and therefore derives `Bot`.
│
*)

Theorem external_fixed_point_reentry_collapses :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalFixedPoint M Gamma chi ->
    regulator_theory_checked_derivable M Gamma
      (formula_negation chi) ->
    regulator_theory_checked_derivable M Gamma Bot.
Proof.
  intros M Gamma chi [_Hforward Hbackward] Hnegchi.
  pose proof
    (regulator_theory_checked_derivable_mp_lemma
       M Gamma (formula_negation chi) chi
       Hbackward Hnegchi) as Hchi.
  exact
    (regulator_theory_checked_derivable_mp_lemma
       M Gamma chi Bot Hnegchi Hchi).
Qed.

(*
│
│          In the M001 specialization a full negation fixed point
│          collapses without an additional branch premise. The forward
│          direction derives `not chi` constructively by assumption,
│          MP, and deduction; the backward direction then recovers
│          `chi`.
│
*)

Theorem external_fixed_point_unconditionally_collapses :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalFixedPoint M Gamma chi ->
    regulator_theory_checked_derivable M Gamma Bot.
Proof.
  intros M Gamma chi [Hforward Hbackward].
  assert (Hnegchi :
    regulator_theory_checked_derivable M Gamma
      (formula_negation chi)).
  {
    apply assumption_discharge.
    apply regulator_theory_checked_derivable_mp_lemma with (A := chi).
    - apply regulator_theory_checked_derivable_mp_lemma with (A := chi).
      + apply checked_derivable_under_assumption.
        exact Hforward.
      + exact (assumption_intro M Gamma chi).
    - exact (assumption_intro M Gamma chi).
  }
  exact
    (external_fixed_point_reentry_collapses
       M Gamma chi (conj Hforward Hbackward) Hnegchi).
Qed.

Theorem external_fixed_point_incompatible_with_mirror_consistency :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalFixedPoint M Gamma chi ->
    MirrorConsistent M Gamma ->
    False.
Proof.
  intros M Gamma chi Hfixed Hconsistent.
  apply Hconsistent.
  exact
    (external_fixed_point_unconditionally_collapses
       M Gamma chi Hfixed).
Qed.

(*
│
│          A hypothetical refutation at a one-way mirror position
│          reconstructs the mirrored formula and collapses the checked
│          theory.
│
*)

Theorem external_mirror_position_reentry_collapses :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    regulator_theory_checked_derivable M Gamma
      (formula_negation chi) ->
    regulator_theory_checked_derivable M Gamma Bot.
Proof.
  intros M Gamma chi Hmirror Hnegchi.
  pose proof
    (regulator_theory_checked_derivable_mp_lemma
       M Gamma (formula_negation chi) chi
       Hmirror Hnegchi) as Hchi.
  exact
    (regulator_theory_checked_derivable_mp_lemma
       M Gamma chi Bot Hnegchi Hchi).
Qed.

(*
│
│          Global mirror consistency implies local consistency at
│          every formula.
│
*)

Theorem mirror_consistency_implies_local_consistency :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    MirrorConsistent M Gamma ->
    MirrorLocallyConsistent M Gamma chi.
Proof.
  intros M Gamma chi Hconsistent Hchi Hnegchi.
  apply Hconsistent.
  exact
    (regulator_theory_checked_derivable_mp_lemma
       M Gamma chi Bot Hnegchi Hchi).
Qed.

(*
│
│          A one-way mirror plus local consistency is the minimal
│          irrefutability theorem.
│
*)

Theorem external_mirror_position_forces_asif_local :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorLocallyConsistent M Gamma chi ->
    AsIF M Gamma chi.
Proof.
  intros M Gamma chi Hmirror Hlocal Hnegchi.
  exact
    (Hlocal
       (regulator_theory_checked_derivable_mp_lemma
          M Gamma (formula_negation chi) chi Hmirror Hnegchi)
       Hnegchi).
Qed.

Theorem external_mirror_position_forces_asif :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    AsIF M Gamma chi.
Proof.
  intros M Gamma chi Hmirror Hconsistent.
  exact
    (external_mirror_position_forces_asif_local
       M Gamma chi Hmirror
       (mirror_consistency_implies_local_consistency
          M Gamma chi Hconsistent)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│            OPTIONAL RELATIVE-CONSISTENCY AND RESPONSE COROLLARIES            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Soundness into a bottom-rejecting predicate yields
│          consistency of the intermediate theory.
│
*)

Theorem world_brain_model_frame_brain_consistent :
  forall (V : EpistemicWorld)
         (brain model : RegulatorTheory)
         (Gamma : Context)
         (frame : WorldBrainModelFrame V brain model Gamma),
    SLambdaConsistent brain Gamma.
Proof.
  intros V brain model Gamma frame Hbot.
  apply (frame_world_consistent frame).
  exact (frame_brain_sound frame Bot Hbot).
Qed.

(*
│
│          The explicit relative-consistency premise transports
│          consistency to the target theory.
│
*)

Theorem world_brain_model_frame_model_consistent :
  forall (V : EpistemicWorld)
         (brain model : RegulatorTheory)
         (Gamma : Context)
         (frame : WorldBrainModelFrame V brain model Gamma),
    MirrorConsistent model Gamma.
Proof.
  intros V brain model Gamma frame.
  exact
    (frame_model_relative_consistency frame
       (world_brain_model_frame_brain_consistent
          V brain model Gamma frame)).
Qed.

(*
│
│          A negative answer re-enters through the question's mirror
│          witness and collapses the model. Consistency therefore
│          excludes a certified `no`.
│
*)

Theorem control_question_negative_answer_impossible :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (question : ControlQuestion M Gamma),
    MirrorConsistent M Gamma ->
    ~ ControlAnswersNo M Gamma question.
Proof.
  intros M Gamma question Hconsistent Hno.
  apply Hconsistent.
  exact
    (external_mirror_position_reentry_collapses
       M Gamma (control_question_formula question)
       (control_question_mirror question) Hno).
Qed.

(*
│
│          Compatibility spelling for
│          `control_question_negative_answer_impossible`; here `no`
│          denotes the explicit negative verdict, not absence of an
│          answer.
│
*)

Theorem control_question_no_answer_impossible :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (question : ControlQuestion M Gamma),
    MirrorConsistent M Gamma ->
    ~ ControlAnswersNo M Gamma question.
Proof.
  exact control_question_negative_answer_impossible.
Qed.

(*
│
│          Binary completeness is used only at this step. Once the
│          interface must choose `yes` or `no`, exclusion of the
│          negative branch forces a positive internal judgment.
│
*)

Theorem control_question_binary_decision_forces_yes :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (question : ControlQuestion M Gamma),
    MirrorConsistent M Gamma ->
    BinaryControlDecision M Gamma question ->
    ControlAnswersYes M Gamma question.
Proof.
  intros M Gamma question Hconsistent [Hyes | Hno].
  - exact Hyes.
  - exfalso.
    exact
      (control_question_negative_answer_impossible
         M Gamma question Hconsistent Hno).
Qed.

Theorem world_brain_model_binary_control_forces_yes :
  forall (V : EpistemicWorld)
         (brain model : RegulatorTheory)
         (Gamma : Context)
         (frame : WorldBrainModelFrame V brain model Gamma)
         (question : ControlQuestion model Gamma),
    BinaryControlDecision model Gamma question ->
    ControlAnswersYes model Gamma question.
Proof.
  intros V brain model Gamma frame question Hdecision.
  exact
    (control_question_binary_decision_forces_yes
       model Gamma question
       (world_brain_model_frame_model_consistent
          V brain model Gamma frame)
       Hdecision).
Qed.

(*
│
│          If the world refutes the control claim and the model is
│          additionally world-sound, a total binary answer is
│          impossible. Relative consistency alone does not assume
│          model soundness, so an internally forced `yes` may instead
│          be externally inaccurate.
│
*)

Theorem world_sound_binary_control_decision_impossible :
  forall (V : EpistemicWorld)
         (brain model : RegulatorTheory)
         (Gamma : Context)
         (frame : WorldBrainModelFrame V brain model Gamma)
         (question : ControlQuestion model Gamma),
    WorldFormulaConsistent V ->
    TheorySoundInWorld V model Gamma ->
    WorldRefutesControlClaim V question ->
    ~ BinaryControlDecision model Gamma question.
Proof.
  intros V brain model Gamma frame question
    Hworld_consistent Hmodel_sound Hworld_no Hdecision.
  pose proof
    (world_brain_model_binary_control_forces_yes
       V brain model Gamma frame question Hdecision) as Hyes.
  apply
    (Hworld_consistent
       (control_question_formula question)
       (Hmodel_sound (control_question_formula question) Hyes)
       Hworld_no).
Qed.

(*
│
│          Every checked theorem supplies a one-way mirror position: K
│          lifts an accepted `A` to `not A -> A`. This witnesses that
│          mirror position is a live proof-theoretic condition rather
│          than the inconsistent full fixed-point equivalence.
│
*)

Theorem checked_derivable_is_external_mirror_position :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    regulator_theory_checked_derivable M Gamma A ->
    ExternalMirrorPosition M Gamma A.
Proof.
  intros M Gamma A HA.
  apply regulator_theory_checked_derivable_mp_lemma with (A := A).
  - apply regulator_theory_axiom_checked_derivable_lemma.
    apply available_axiom_bool_k_lemma.
  - exact HA.
Qed.

(*
│
│          A locally consistent one-way mirror excludes coded
│          recognition acceptance.
│
*)

Theorem coded_recognition_acceptance_excluded_local :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorLocallyConsistent M Gamma chi ->
    ~ CodedRecognitionAccepted M Gamma chi.
Proof.
  intros M Gamma chi Hmirror Hlocal Haccepted.
  apply
    (external_mirror_position_forces_asif_local
       M Gamma chi Hmirror Hlocal).
  exact (coded_recognition_reenters_regulator M Gamma chi Haccepted).
Qed.

(*
│
│          The global-consistency form is a compatibility corollary of
│          the local theorem.
│
*)

Theorem coded_recognition_acceptance_excluded :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    ~ CodedRecognitionAccepted M Gamma chi.
Proof.
  intros M Gamma chi Hmirror Hconsistent.
  exact
    (coded_recognition_acceptance_excluded_local
       M Gamma chi Hmirror
       (mirror_consistency_implies_local_consistency
          M Gamma chi Hconsistent)).
Qed.

Theorem coded_recognition_opacity :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    ~ CodedInternalFixedPointRecognition M Gamma chi.
Proof.
  exact coded_recognition_acceptance_excluded.
Qed.

(*
│
│          Legacy corollary: the already inconsistent conjunction of a
│          full fixed point and consistency excludes a checked
│          refutation certificate. The live theorem below uses only an
│          external mirror position.
│
*)

Theorem external_fixed_point_excludes_checked_refutation_recognition :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalFixedPoint M Gamma chi ->
    MirrorConsistent M Gamma ->
    CheckedRefutationRecognitionCertificate M Gamma chi ->
    False.
Proof.
  intros M Gamma chi Hfixed Hconsistent Hcertificate.
  apply
    (external_mirror_position_forces_asif
       M Gamma chi (proj2 Hfixed) Hconsistent).
  apply regulator_theory_proof_certificate_derivable_lemma.
  exact Hcertificate.
Qed.

Theorem external_mirror_position_excludes_checked_refutation_recognition :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    MirrorConsistent M Gamma ->
    CheckedRefutationRecognitionCertificate M Gamma chi ->
    False.
Proof.
  intros M Gamma chi Hmirror Hconsistent Hcertificate.
  apply
    (external_mirror_position_forces_asif
       M Gamma chi Hmirror Hconsistent).
  apply regulator_theory_proof_certificate_derivable_lemma.
  exact Hcertificate.
Qed.

(*
│
│          M-to-Slambda inclusion transports an M-derivation of `Bot`
│          outward, so Slambda-consistency implies M-consistency.
│
*)

Theorem outer_consistency_implies_mirror_consistency :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context),
    regulator_theory_included M Slambda ->
    SLambdaConsistent Slambda Gamma ->
    MirrorConsistent M Gamma.
Proof.
  intros Slambda M Gamma Hincluded Hconsistent Hbot.
  apply Hconsistent.
  exact
    (regulator_theory_checked_derivable_regulator_theory_monotone_lemma
       M Slambda Gamma Bot Hincluded Hbot).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                MIRROR OPACITY                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Under inclusion and outer consistency, a one-way mirror
│          position is assumption-licensed but has no adequate
│          internal recognition certificate.
│
*)

Theorem mirror_opacity :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (recognition_claim : FixedPointRecognitionCoding)
         (chi : Formula),
    regulator_theory_included M Slambda ->
    SLambdaConsistent Slambda Gamma ->
    ExternalMirrorPosition M Gamma chi ->
    RecognitionAdequacy M Gamma recognition_claim chi ->
    AssumptionLicensedContent M Gamma chi /\
    ~ InternalFixedPointRecognition
        M Gamma recognition_claim chi.
Proof.
  intros Slambda M Gamma recognition_claim chi
    Hincluded Hconsistent Hmirror Hadequate.
  pose proof
    (outer_consistency_implies_mirror_consistency
       Slambda M Gamma Hincluded Hconsistent) as HMconsistent.
  pose proof
    (external_mirror_position_forces_asif
       M Gamma chi Hmirror HMconsistent) as Hasif.
  split.
  - exact
      (licensed_assumption_yields_assumption_licensed_content
         M Gamma chi Hasif).
  - exact
      (recognition_adequacy_excludes_legacy_internal_recognition
         M Gamma recognition_claim chi Hadequate).
Qed.

(*
│
│          The fixed-regulator wrapper supplies inclusion,
│          consistency, recognition coding, and adequacy to
│          `mirror_opacity`.
│
*)

Theorem fixed_regulator_mirror_opacity :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         (chi : Formula),
    ExternalMirrorPosition M Gamma chi ->
    AssumptionLicensedContent M Gamma chi /\
    ~ InternalFixedPointRecognition
        M Gamma (fixed_recognition_claim S) chi.
Proof.
  intros Slambda M Gamma S chi Hmirror.
  exact
    (mirror_opacity
       Slambda M Gamma (fixed_recognition_claim S) chi
       (fixed_regulator_inclusion S)
       (fixed_regulator_consistency S)
       Hmirror
       (fixed_recognition_adequacy S chi Hmirror)).
Qed.

(*
│
│          Legacy full-frame wrapper with jointly inconsistent
│          premises. `E` constructs a full fixed point and therefore
│          `Bot` in `M`; `fixed_regulator_inclusion S` transports that
│          derivation into `Slambda`, contradicting
│          `fixed_regulator_consistency S`. Consequently this theorem
│          is not a live consistency result and is excluded from
│          `WITNESS`. Use `fixed_regulator_mirror_opacity` with a
│          supplied `ExternalMirrorPosition` for the live interface.
│
*)

Theorem l001_mirror_opacity :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (S : FixedSymbolicRegulator Slambda M Gamma)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    exists chi : Formula,
      ExternalFixedPoint M Gamma chi /\
      AssumptionLicensedContent M Gamma chi /\
      ~ InternalFixedPointRecognition
          M Gamma (fixed_recognition_claim S) chi.
Proof.
  intros Slambda M Gamma S Code E.
  destruct (l001_constructs_external_fixed_point M Gamma Code E)
    as [chi Hfixed].
  exists chi.
  split.
  - exact Hfixed.
  - exact
      (fixed_regulator_mirror_opacity
         Slambda M Gamma S chi (proj2 Hfixed)).
Qed.
