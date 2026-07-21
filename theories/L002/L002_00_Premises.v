(*L002_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / L002_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Premise layer for L002/SYMBOLIC REGULATION. L002 isolates two related
  constraints on self-referential evaluation. A full negation fixed point
  collapses checked derivability. Separately, the live consistent results
  take a supplied one-way mirror position: consistency yields internal
  non-refutability, while successful adequate recognition reconstructs the
  missing diagonal direction and re-enters collapse. Later interfaces expose
  pointwise finite-depth persistence, finite-state operation, and optional
  attribution, provenance, and externalization responses.

  Constraint reading. At a supplied one-way mirror position, consistency and
  successful actionable recognition cannot coexist: accepted adequate
  recognition supplies the missing fixed-point direction and thereby
  reconstructs collapse. A concrete evaluator may realize a related
  obstruction by restricting representation or disclosure, returning
  `unknown`, stratifying evaluators, diverging, or exhausting resources only
  when an additional operational model connects those behaviors to the
  proof-theoretic interfaces. L002 itself selects and certifies no such
  failure mode.

  Scope guardrail. L002 certifies syntactic irrefutability, re-entry
  obstruction, recognition opacity, pointwise persistence at every supplied
  finite mirror depth, and recurrence for explicitly finite state carriers.
  Its vocabulary does not by itself identify truth, belief, agency, causal
  source, independently verified origin, psychological dissociation,
  nontermination, or machine failure. Such identifications require a separate
  model of the concrete system. Formal non-closure alone supports neither a
  positive nor a negative metaphysical attribution.

*)

From L001 Require Export L001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            REGULATED ASSUMPTIONS                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A regulated assumption is a formula-indexed predicate
│          relative to a regulator theory and context.
│
*)

Definition RegulatedAssumption : Type :=
  RegulatorTheory -> Context -> Formula -> Prop.

(*
│
│          `AsIF M Gamma A` means exactly that `M` has no checked
│          derivation of the object-level negation of `A` from
│          `Gamma`. It is the non-refutation component of L002's
│          assumption-licensed continuation status; ordinary context
│          extension, not `AsIF` itself, supplies derivability under
│          assumption `A`. It is not by itself truth, belief,
│          probability, voluntary control, or global commitment.
│
*)

Definition AsIF
    (M : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Prop :=
  ~ regulator_theory_checked_derivable
      M Gamma (formula_negation A).

(*
│
│          `AssumptionLicensed` is the regulated-assumption spelling
│          of `AsIF`.
│
*)

Definition AssumptionLicensed : RegulatedAssumption :=
  AsIF.

(*
│
│          `UnderAssumption M Gamma A B` is checked derivability of
│          `B` from the extended context `A :: Gamma`.
│
*)

Definition UnderAssumption
    (M : RegulatorTheory)
    (Gamma : Context)
    (A B : Formula) : Prop :=
  regulator_theory_checked_derivable M (ctx_extend A Gamma) B.

(*
│
│          `AssumptionLicensedContent` packages non-refutability of
│          `A` with availability of `A` in its own explicitly extended
│          context. It does not assert autonomous acceptance or
│          forcing of `A`.
│
*)

Definition AssumptionLicensedContent
    (M : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Prop :=
  AsIF M Gamma A /\
  UnderAssumption M Gamma A A.

(*
│
│          `ForcedContent` is retained as a compatibility alias. The
│          preferred name is `AssumptionLicensedContent`, since the
│          second conjunct is availability by the ordinary assumption
│          rule rather than an autonomous forcing principle.
│
*)

Definition ForcedContent :=
  AssumptionLicensedContent.

(*
│
│          `AsIFContinuation` combines non-refutability of `A` with
│          checked derivability of `B` under `A`.
│
*)

Definition AsIFContinuation
    (M : RegulatorTheory)
    (Gamma : Context)
    (A B : Formula) : Prop :=
  AsIF M Gamma A /\
  UnderAssumption M Gamma A B.

(*
│
│          The head formula of an extended context has a one-line
│          checked assumption proof.
│
*)

Theorem assumption_intro :
  forall (M : RegulatorTheory) (Gamma : Context) (A : Formula),
    UnderAssumption M Gamma A A.
Proof.
  intros M Gamma A.
  unfold UnderAssumption, ctx_extend.
  apply regulator_theory_assumption_checked_derivable_lemma.
  simpl.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

(*
│
│          Compatibility spelling: every `AsIF` formula satisfies the
│          legacy `ForcedContent` alias because it is available under
│          its own assumption.
│
*)

Theorem licensed_assumption_forces_content :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    AsIF M Gamma A ->
    ForcedContent M Gamma A.
Proof.
  intros M Gamma A Hasif.
  split.
  - exact Hasif.
  - exact (assumption_intro M Gamma A).
Qed.

(*
│
│          Preferred literal spelling of the compatibility theorem
│          above.
│
*)

Theorem licensed_assumption_yields_assumption_licensed_content :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    AsIF M Gamma A ->
    AssumptionLicensedContent M Gamma A.
Proof.
  exact licensed_assumption_forces_content.
Qed.

(*
│
│          Every base-context checked derivation remains available
│          after extending the context by one assumption.
│
*)

Theorem checked_derivable_under_assumption :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A B : Formula),
    regulator_theory_checked_derivable M Gamma B ->
    UnderAssumption M Gamma A B.
Proof.
  intros M Gamma A B Hderivable.
  unfold UnderAssumption.
  apply regulator_theory_checked_derivable_context_monotone_lemma
    with (Gamma := Gamma).
  - unfold context_included.
    intros C Hmember.
    exact (ctx_mem_bool_extend_preserve_lemma C A Gamma Hmember).
  - exact Hderivable.
Qed.

(*
│
│          M001 deduction discharges an assumption-relative derivation
│          of `B` into a base-context derivation of `A -> B`.
│
*)

Theorem assumption_discharge :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A B : Formula),
    UnderAssumption M Gamma A B ->
    regulator_theory_checked_derivable M Gamma (Imp A B).
Proof.
  intros M Gamma A B Hunder.
  exact
    (regulator_theory_checked_derivable_deduction_lemma
       M Gamma A B Hunder).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                 MIRROR POSITION AT THE META/OBJECT BOUNDARY                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `ExternalFixedPoint M Gamma chi` is L001
│          negation-fixed-point equivalence specialized to M001
│          checked derivability. The legacy word `External` marks that
│          the fixed-point condition is supplied at the metatheoretic
│          interface to `M`; it does not assert an external causal
│          source.
│
*)

Definition ExternalFixedPoint
    (M : RegulatorTheory)
    (Gamma : Context)
    (chi : Formula) : Prop :=
  NegationFixedPointFor
    (regulator_theory_checked_derivable M Gamma)
    chi.

(*
│
│          `ExternalMirrorPosition M Gamma chi` retains only the
│          non-collapsing re-entry direction `not chi -> chi`. Unlike
│          a full negation fixed point, this supplied premise is
│          compatible in shape with M001 consistency and is sufficient
│          for the L002 irrefutability argument. Here too `External`
│          is interface-relative rather than causal: the formal
│          content is exactly the displayed checked-derivability
│          condition.
│
*)

Definition ExternalMirrorPosition
    (M : RegulatorTheory)
    (Gamma : Context)
    (chi : Formula) : Prop :=
  regulator_theory_checked_derivable M Gamma
    (Imp (formula_negation chi) chi).

(*
│
│          `MirrorConsistent M Gamma` excludes a checked M-derivation
│          of `Bot` from `Gamma`.
│
*)

Definition MirrorConsistent
    (M : RegulatorTheory)
    (Gamma : Context) : Prop :=
  ~ regulator_theory_checked_derivable M Gamma Bot.

(*
│
│          `SLambdaConsistent Slambda Gamma` is the corresponding
│          consistency predicate for the enclosing regulator.
│
*)

Definition SLambdaConsistent
    (Slambda : RegulatorTheory)
    (Gamma : Context) : Prop :=
  ~ regulator_theory_checked_derivable Slambda Gamma Bot.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       WORLD, BRAIN, MODEL, AND CONTROL                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An `EpistemicWorld` is an external interpretation of M001
│          formulas. No semantic law is built into the carrier: bottom
│          rejection, formula consistency, and theory soundness are
│          supplied separately so that applications must expose every
│          bridge premise.
│
*)

Definition EpistemicWorld : Type :=
  Formula -> Prop.

Definition WorldConsistent
    (V : EpistemicWorld) : Prop :=
  ~ V Bot.

Definition WorldFormulaConsistent
    (V : EpistemicWorld) : Prop :=
  forall A : Formula,
    V A ->
    V (formula_negation A) ->
    False.

Definition TheorySoundInWorld
    (V : EpistemicWorld)
    (T : RegulatorTheory)
    (Gamma : Context) : Prop :=
  forall A : Formula,
    regulator_theory_checked_derivable T Gamma A ->
    V A.

(*
│
│          `WorldBrainModelFrame V brain model Gamma` makes the
│          relative-consistency chain explicit. The brain is sound in
│          a world rejecting `Bot`, and every model derivation is
│          available to the brain through regulator inclusion. The
│          frame does not assume that the embedded model is
│          independently sound in the world.
│
*)

Record WorldBrainModelFrame
    (V : EpistemicWorld)
    (brain model : RegulatorTheory)
    (Gamma : Context) : Type := {
  frame_world_consistent : WorldConsistent V;
  frame_brain_sound : TheorySoundInWorld V brain Gamma;
  frame_model_inclusion : regulator_theory_included model brain
}.

Arguments frame_world_consistent {V brain model Gamma} _.
Arguments frame_brain_sound {V brain model Gamma} _ _ _.
Arguments frame_model_inclusion {V brain model Gamma} _.

(*
│
│          A `ControlQuestion` packages the formula read as “I am in
│          control” together with its explicit one-way mirror witness
│          `not C -> C`. The self-referential or causal reading is
│          therefore not inferred from an arbitrary formula alone.
│
*)

Record ControlQuestion
    (M : RegulatorTheory)
    (Gamma : Context) : Type := {
  control_question_formula : Formula;
  control_question_mirror :
    ExternalMirrorPosition M Gamma control_question_formula
}.

Arguments control_question_formula {M Gamma} _.
Arguments control_question_mirror {M Gamma} _.

Definition ControlAnswersYes
    (M : RegulatorTheory)
    (Gamma : Context)
    (question : ControlQuestion M Gamma) : Prop :=
  regulator_theory_checked_derivable
    M Gamma (control_question_formula question).

Definition ControlAnswersNo
    (M : RegulatorTheory)
    (Gamma : Context)
    (question : ControlQuestion M Gamma) : Prop :=
  regulator_theory_checked_derivable
    M Gamma (formula_negation (control_question_formula question)).

Definition BinaryControlDecision
    (M : RegulatorTheory)
    (Gamma : Context)
    (question : ControlQuestion M Gamma) : Prop :=
  ControlAnswersYes M Gamma question \/
  ControlAnswersNo M Gamma question.

Definition WorldRefutesControlClaim
    (V : EpistemicWorld)
    {M : RegulatorTheory}
    {Gamma : Context}
    (question : ControlQuestion M Gamma) : Prop :=
  V (formula_negation (control_question_formula question)).

(*
│
│          The operational control-response alphabet distinguishes a
│          positive answer, a negative answer, and reflective
│          re-entry. File 02 connects these tags to recursive mirror
│          formulas.
│
*)

Inductive ControlResponse : Type :=
| control_response_yes
| control_response_no
| control_response_reenter.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           RECOGNITION AND RE-ENTRY                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `CodedRecognitionClaim` is L002's explicitly defined
│          recognition object language. Its constructor carries the
│          M001 formula syntax being claimed as a negation fixed
│          point, making recognition claims first-class regulator
│          outputs without adding constructors to M001 `Formula`. In
│          the core obstruction, accepted recognition evidence has one
│          exact technical role: it supplies `A -> not A`, the missing
│          diagonal direction, and its executable re-entry under
│          assumption `A` yields `not A`. The constructor alone
│          establishes no psychological self-recognition, belief,
│          agency, or causal provenance.
│
*)

Inductive CodedRecognitionClaim : Type :=
| recognizes_fixed_point : Formula -> CodedRecognitionClaim.

Definition coded_recognition_subject
    (claim : CodedRecognitionClaim) : Formula :=
  match claim with
  | recognizes_fixed_point A => A
  end.

(*
│
│          A coded recognition certificate retains its advertised
│          formula and a finite M001 evidence script for the missing
│          diagonal direction `A -> not A`. Re-entry is computed
│          separately.
│
*)

Record CodedRecognitionCertificate : Type := {
  coded_recognition_certificate_subject : Formula;
  coded_recognition_evidence_script : Proof
}.

(*
│
│          Recognition evidence is the missing diagonal direction `A
│          -> not A`. A one-way mirror position supplies only `not A
│          -> A`; successful recognition supplies this converse
│          without checking the re-entry conclusion directly.
│
*)

Definition coded_recognition_evidence_formula (A : Formula) : Formula :=
  Imp A (formula_negation A).

(*
│
│          The total evidence checker first matches the certificate's
│          advertised subject against the claim and then runs the
│          unchanged M001 checker on `A -> not A` in the base context.
│          This totality is verification of each supplied finite
│          certificate; it is not proof search, universal certificate
│          generation, or a total semantic recognition classifier.
│
*)

Definition coded_recognition_certificate_check_bool
    (M : RegulatorTheory)
    (Gamma : Context)
    (certificate : CodedRecognitionCertificate)
    (claim : CodedRecognitionClaim) : bool :=
  match claim with
  | recognizes_fixed_point A =>
      formula_eq_bool
        certificate.(coded_recognition_certificate_subject) A &&
      regulator_theory_check_bool
        M Gamma
        certificate.(coded_recognition_evidence_script)
        (coded_recognition_evidence_formula A)
  end.

Definition coded_recognition_assumption_script (A : Formula) : Proof :=
  [pl_assumption A].

(*
│
│          The re-entry transform is executable proof composition. It
│          applies the checked evidence `A -> not A` to the one-line
│          assumption proof of `A`, producing a finite script whose
│          target is `not A`.
│
*)

Definition coded_recognition_reentry_transform
    (A : Formula)
    (evidence_script : Proof) : Proof :=
  regulator_theory_mp_compose
    (formula_negation A)
    evidence_script
    (coded_recognition_assumption_script A).

(*
│
│          The recognition checker is packaged through M001's frozen
│          generic symbolic-regulator interface: finite certificates
│          are instructions, coded recognition claims are outputs, and
│          acceptance is the Boolean checker above.
│
*)

Definition coded_recognition_regulator
    (M : RegulatorTheory)
    (Gamma : Context) : S_λ :=
  {|
    symbolic_regulator_output := CodedRecognitionClaim;
    symbolic_regulator_instruction := CodedRecognitionCertificate;
    symbolic_regulator_accepts_bool :=
      coded_recognition_certificate_check_bool M Gamma
  |}.

Definition CodedRecognitionAccepted
    (M : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Prop :=
  symbolic_regulator_derivable
    (coded_recognition_regulator M Gamma)
    (recognizes_fixed_point A).

(*
│
│          Evidence-checker soundness exposes the accepted recognition
│          evidence as a checked derivation of the missing diagonal
│          direction, not yet as its re-entry consequence.
│
*)

Theorem coded_recognition_certificate_check_sound :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (certificate : CodedRecognitionCertificate)
         (A : Formula),
    coded_recognition_certificate_check_bool
      M Gamma certificate (recognizes_fixed_point A) = true ->
    regulator_theory_checked_derivable M Gamma
      (coded_recognition_evidence_formula A).
Proof.
  intros M Gamma [subject script] A Hcheck.
  unfold coded_recognition_certificate_check_bool in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hsubject Hscript].
  apply formula_eq_bool_true_lemma in Hsubject.
  subst subject.
  exists script.
  exact Hscript.
Qed.

Theorem coded_recognition_assumption_script_checked :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    regulator_theory_check_bool
      M (ctx_extend A Gamma)
      (coded_recognition_assumption_script A) A = true.
Proof.
  intros M Gamma A.
  unfold coded_recognition_assumption_script,
    regulator_theory_check_bool,
    proof_script_check_from_bool,
    proof_line_valid_bool,
    pl_assumption.
  rewrite ctx_mem_bool_extend_self_lemma.
  simpl.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

(*
│
│          The checked re-entry theorem is the load-bearing bridge:
│          accepted evidence and the assumed subject are composed by
│          the executable M001 MP transformer into a checked proof of
│          `not A`.
│
*)

Theorem coded_recognition_reentry_transform_checked :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (certificate : CodedRecognitionCertificate)
         (A : Formula),
    coded_recognition_certificate_check_bool
      M Gamma certificate (recognizes_fixed_point A) = true ->
    regulator_theory_check_bool
      M (ctx_extend A Gamma)
      (coded_recognition_reentry_transform
         A certificate.(coded_recognition_evidence_script))
      (formula_negation A) = true.
Proof.
  intros M Gamma [subject evidence_script] A Haccepted.
  unfold coded_recognition_certificate_check_bool in Haccepted.
  simpl in Haccepted.
  apply andb_true_iff in Haccepted.
  destruct Haccepted as [Hsubject Hevidence].
  apply formula_eq_bool_true_lemma in Hsubject.
  subst subject.
  assert (Hevidence_extended :
    regulator_theory_check_bool
      M (ctx_extend A Gamma) evidence_script
      (coded_recognition_evidence_formula A) = true).
  {
    apply regulator_theory_check_bool_context_monotone_lemma
      with (Gamma := Gamma).
    - unfold context_included.
      intros B Hmember.
      exact (ctx_mem_bool_extend_preserve_lemma B A Gamma Hmember).
    - exact Hevidence.
  }
  unfold coded_recognition_reentry_transform.
  apply regulator_theory_mp_compose_checked_lemma
    with (A := A).
  - exact Hevidence_extended.
  - exact (coded_recognition_assumption_script_checked M Gamma A).
Qed.

Theorem coded_recognition_acceptance_evidence :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    CodedRecognitionAccepted M Gamma A ->
    regulator_theory_checked_derivable M Gamma
      (coded_recognition_evidence_formula A).
Proof.
  intros M Gamma A [certificate Haccepted].
  exact
    (coded_recognition_certificate_check_sound
       M Gamma certificate A Haccepted).
Qed.

Theorem coded_recognition_evidence_acceptance_complete :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    regulator_theory_checked_derivable M Gamma
      (coded_recognition_evidence_formula A) ->
    CodedRecognitionAccepted M Gamma A.
Proof.
  intros M Gamma A [evidence_script Hevidence].
  unfold CodedRecognitionAccepted,
    symbolic_regulator_derivable.
  exists
    {| coded_recognition_certificate_subject := A;
       coded_recognition_evidence_script := evidence_script |}.
  unfold coded_recognition_regulator.
  simpl.
  unfold coded_recognition_certificate_check_bool.
  simpl.
  rewrite formula_eq_bool_refl_lemma.
  exact Hevidence.
Qed.

Theorem coded_recognition_acceptance_iff_evidence :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    CodedRecognitionAccepted M Gamma A <->
    regulator_theory_checked_derivable M Gamma
      (coded_recognition_evidence_formula A).
Proof.
  intros M Gamma A.
  split.
  - exact (coded_recognition_acceptance_evidence M Gamma A).
  - exact (coded_recognition_evidence_acceptance_complete M Gamma A).
Qed.

Theorem coded_recognition_acceptance_sound :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    CodedRecognitionAccepted M Gamma A ->
    UnderAssumption M Gamma A (formula_negation A).
Proof.
  intros M Gamma A [certificate Haccepted].
  unfold UnderAssumption.
  exists
    (coded_recognition_reentry_transform
       A certificate.(coded_recognition_evidence_script)).
  exact
    (coded_recognition_reentry_transform_checked
       M Gamma certificate A Haccepted).
Qed.

(*
│
│          `CodedInternalFixedPointRecognition` is retained as a
│          compatibility name for acceptance by the first-class coded
│          recognition regulator. `AsIF` is deliberately not conjoined
│          here: accepted evidence yields `not A`, while `AsIF` denies
│          such a checked derivation. Keeping the two predicates
│          separate makes mirror consistency responsible for the
│          opacity theorem.
│
*)

Definition CodedInternalFixedPointRecognition
    (M : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Prop :=
  CodedRecognitionAccepted M Gamma A.

(*
│
│          A fixed-point recognition coding maps a formula to the
│          formula intended to certify its fixed-point status.
│
*)

Definition FixedPointRecognitionCoding : Type :=
  Formula -> Formula.

(*
│
│          The concrete refutation-recognition coding represents
│          recognition of `A` by the literal object-level claim `not
│          A`. It is intentionally narrow: unlike an epistemic coding,
│          its meaning is fixed directly by the checked proof target.
│
*)

Definition refutation_recognition_claim :
    FixedPointRecognitionCoding :=
  formula_negation.

(*
│
│          A checked refutation-recognition certificate retains the
│          finite M001 proof script whose checked target is the
│          concrete recognition claim `not A`.
│
*)

Definition CheckedRefutationRecognitionCertificate
    (M : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Type :=
  regulator_theory_proof_certificate
    M Gamma (refutation_recognition_claim A).

(*
│
│          Recognition is adequate at `chi` when accepting its
│          certificate under `chi` reconstructs `not chi` in the same
│          extended context.
│
*)

Definition RecognitionAdequacy
    (M : RegulatorTheory)
    (Gamma : Context)
    (recognition_claim : FixedPointRecognitionCoding)
    (chi : Formula) : Prop :=
  UnderAssumption M Gamma chi (recognition_claim chi) ->
  UnderAssumption M Gamma chi (formula_negation chi).

(*
│
│          Internal fixed-point recognition combines `AsIF chi` with
│          acceptance of its recognition certificate under `chi`.
│
*)

Definition InternalFixedPointRecognition
    (M : RegulatorTheory)
    (Gamma : Context)
    (recognition_claim : FixedPointRecognitionCoding)
    (chi : Formula) : Prop :=
  AsIF M Gamma chi /\
  UnderAssumption M Gamma chi (recognition_claim chi).

(*
│
│          A fixed symbolic regulator packages recognition coding,
│          M-to-Slambda inclusion, outer consistency, and adequacy at
│          every one-way external mirror position.
│
*)

Record FixedSymbolicRegulator
    (Slambda M : RegulatorTheory)
    (Gamma : Context) : Type := {
  fixed_recognition_claim : FixedPointRecognitionCoding;

  fixed_regulator_inclusion :
    regulator_theory_included M Slambda;

  fixed_regulator_consistency :
    SLambdaConsistent Slambda Gamma;

  fixed_recognition_adequacy :
    forall chi : Formula,
      ExternalMirrorPosition M Gamma chi ->
      RecognitionAdequacy
        M Gamma fixed_recognition_claim chi
}.

(*
│
│          Projection arguments keep the regulator parameters implicit
│          at downstream call sites.
│
*)

Arguments fixed_recognition_claim {Slambda M Gamma} _ _.
Arguments fixed_regulator_inclusion {Slambda M Gamma} _.
Arguments fixed_regulator_consistency {Slambda M Gamma} _.
Arguments fixed_recognition_adequacy {Slambda M Gamma} _ _ _.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                    OPERATIONAL AND ATTRIBUTION INTERFACES                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition ActiveSchemaSet : Type := list Formula.

Definition SchemaSelected
    (active : ActiveSchemaSet) (A : Formula) : Prop :=
  In A active.

Record FiniteOperationalLayer (State : Type) : Type := {
  finite_operational_states : list State;
  operational_state_eq_dec :
    forall x y : State, {x = y} + {x <> y};
  operational_state_at : nat -> State;
  operational_state_enumerated :
    forall time : nat,
      In (operational_state_at time) finite_operational_states
}.

Arguments finite_operational_states {State} _.
Arguments operational_state_eq_dec {State} _ _ _.
Arguments operational_state_at {State} _ _.
Arguments operational_state_enumerated {State} _ _.

(*
│
│          `AttributionCoding` is a caller-supplied formula
│          transformer. Naming two instances `internal_attribution`
│          and `external_attribution` stipulates two object-language
│          codings; the names do not force either coding to track real
│          causal origin. No bridge from recognition opacity or
│          non-refutation to actual provenance is built into this
│          type.
│
*)

Definition AttributionCoding : Type := Formula -> Formula.

(*
│
│          `AttributionResponse` is an explicit bridge law from base
│          irrefutability to at least one supplied attribution coding.
│          It is not derived from mirror opacity and should be read as
│          an empirical or model-specific response hypothesis when
│          applied to a real system.
│
*)

Definition AttributionResponse
    (M : RegulatorTheory) (Gamma : Context)
    (internal_attribution external_attribution : AttributionCoding) : Prop :=
  forall A : Formula,
    AsIF M Gamma A ->
    AsIF M Gamma (internal_attribution A) \/
    AsIF M Gamma (external_attribution A).

Definition SelectedAttributionResponse
    (M : RegulatorTheory) (Gamma : Context)
    (active : ActiveSchemaSet)
    (internal_attribution external_attribution : AttributionCoding) : Prop :=
  forall A : Formula,
    SchemaSelected active A ->
    AsIF M Gamma A ->
    AsIF M Gamma (internal_attribution A) \/
    AsIF M Gamma (external_attribution A).

(*
│
│          `AttributionallyAmbiguous` is the attributional standoff
│          condition: both supplied provenance formulas are
│          simultaneously `AsIF`. It expresses no preference,
│          probability shift, or metaphysical lean toward either
│          attribution.
│
*)

Definition AttributionallyAmbiguous
    (M : RegulatorTheory) (Gamma : Context)
    (internal_attribution external_attribution : AttributionCoding)
    (A : Formula) : Prop :=
  AsIF M Gamma (internal_attribution A) /\
  AsIF M Gamma (external_attribution A).

Definition AttributionalAmbiguityResponse
    (M : RegulatorTheory) (Gamma : Context)
    (internal_attribution external_attribution : AttributionCoding) : Prop :=
  forall A : Formula,
    AsIF M Gamma A ->
    AttributionallyAmbiguous
      M Gamma internal_attribution external_attribution A.

Definition OpacityExternalAttributionResponse
    (M : RegulatorTheory) (Gamma : Context)
    (recognition_claim : FixedPointRecognitionCoding)
    (external_attribution : AttributionCoding) : Prop :=
  forall A : Formula,
    AsIF M Gamma A ->
    ~ InternalFixedPointRecognition M Gamma recognition_claim A ->
    AsIF M Gamma (external_attribution A).

Record LogicalOperationalLayer
    (State : Type) (M : RegulatorTheory) (Gamma : Context) : Type := {
  logical_finite_operation : FiniteOperationalLayer State;
  logical_operational_step : State -> State;
  logical_operational_trace_successor :
    forall time : nat,
      operational_state_at logical_finite_operation (S time) =
      logical_operational_step
        (operational_state_at logical_finite_operation time);
  logical_operational_content : State -> Formula;
  logical_operational_content_asif :
    forall time : nat,
      AsIF M Gamma
        (logical_operational_content
           (operational_state_at logical_finite_operation time));
  logical_operational_content_opaque :
    forall time : nat,
      ~ CodedRecognitionAccepted M Gamma
          (logical_operational_content
             (operational_state_at logical_finite_operation time))
}.

Arguments logical_finite_operation {State M Gamma} _.
Arguments logical_operational_step {State M Gamma} _ _.
Arguments logical_operational_trace_successor {State M Gamma} _ _.
Arguments logical_operational_content {State M Gamma} _ _.
Arguments logical_operational_content_asif {State M Gamma} _ _.
Arguments logical_operational_content_opaque {State M Gamma} _ _.

Record SelectedOperationalAttributionLayer
    (State : Type) (M : RegulatorTheory) (Gamma : Context)
    (internal_attribution external_attribution : AttributionCoding) : Type := {
  selected_logical_operation : LogicalOperationalLayer State M Gamma;
  selected_operational_schemas : ActiveSchemaSet;
  selected_operational_content_selected :
    forall time : nat,
      SchemaSelected selected_operational_schemas
        (logical_operational_content selected_logical_operation
           (operational_state_at
              (logical_finite_operation selected_logical_operation) time));
  selected_operational_attribution_response :
    SelectedAttributionResponse
      M Gamma selected_operational_schemas
      internal_attribution external_attribution
}.

Arguments selected_logical_operation
  {State M Gamma internal_attribution external_attribution} _.
Arguments selected_operational_schemas
  {State M Gamma internal_attribution external_attribution} _.
Arguments selected_operational_content_selected
  {State M Gamma internal_attribution external_attribution} _ _.
Arguments selected_operational_attribution_response
  {State M Gamma internal_attribution external_attribution} _.

(*
│
│          `Provenance` is an explicitly defined two-tag type for
│          operational attribution. The constructors encode the labels
│          `internal` and `external`; they do not certify an
│          independently verified causal origin.
│
*)

Inductive Provenance : Type :=
| provenance_internal
| provenance_external.

(*
│
│          `CodedAttributionObservation` pairs logical content with
│          one stipulated provenance tag. Observation of a tag is not
│          observation of the real origin named by that tag.
│
*)

Inductive CodedAttributionObservation : Type :=
| observes_provenance :
    Formula -> Provenance -> CodedAttributionObservation.

(* The layer records the system's attribution of provenance; it does not
   assert an independently verified origin for the state. *)
Record AttributedProvenanceOperationalLayer
    (State : Type) (M : RegulatorTheory) (Gamma : Context) : Type := {
  attributed_provenance_logical_operation : LogicalOperationalLayer State M Gamma;
  operational_state_attributed_provenance : State -> Provenance
}.

Arguments attributed_provenance_logical_operation {State M Gamma} _.
Arguments operational_state_attributed_provenance {State M Gamma} _ _.

Definition ExternalizationRelation (System : Type) : Type :=
  System -> Formula -> Prop.

Definition ExternalizationResponse
    (System : Type) (M : RegulatorTheory) (Gamma : Context)
    (externalizes : ExternalizationRelation System)
    (system : System) : Prop :=
  forall A : Formula,
    AsIF M Gamma A ->
    externalizes system A.
