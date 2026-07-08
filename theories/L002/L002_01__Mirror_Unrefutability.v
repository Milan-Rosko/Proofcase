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

  The central result of this file is that an inner system embedded within
  `Sλ` cannot, while remaining consistent, internally refute the sentence
  whose role is to assert its match with the system regulating it. An
  internal refutation of such a sentence forces its derivation, contradicting
  consistency. The result is given in four progressively packaged forms — the
  proof-minimal kernel, the public wrapper, the construction supplying the
  witness from the L001 evaluation closure, and the fully discharged form —
  together with two structural consequences: an exclusion result for
  externally supported content, and the operational non-escape invariant
  under which an attempted internal escape collapses `Sλ`.

*)

From L002 Require Export L002_00__Premises.
From L001 Require Export L001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            MIRROR UNREFUTABILITY                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `mirror_unrefutability_core` states the proof-minimal
│          kernel: a consistent inner system carrying the M-side Curry
│          property of the witness sentence cannot refute that
│          sentence. The wrapper, the L001-backed construction, and
│          the discharged form below all reduce to this result.
│
*)

(*            ChiEqMInternal(M, Γ, χ_eq) ∧ M ⊬_Γ ⊥ ⇒ M ⊬_Γ ¬χ_eq.             *)

Theorem mirror_unrefutability_core :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi_eq : DiagonalFormula),
    ChiEqMInternal M Gamma chi_eq ->
    MirrorConsistent M Gamma ->
    ~ regulator_theory_checked_derivable M Gamma
        (formula_negation chi_eq).
Proof.
  intros M Gamma chi_eq HMint Hconsistent Hrefute.
  apply Hconsistent.
  apply regulator_theory_checked_derivable_mp_lemma with (A := chi_eq).
  - exact Hrefute.
  - exact (HMint Hrefute).
Qed.

(*
│
│          `mirror_unrefutability` is the public form, stated against
│          the full mirror interface: inclusion, the two coding
│          hypotheses, and the `Sλ`-side diagonal reading. The proof
│          shows these hypotheses are not load-bearing; the wrapper
│          delegates to the kernel and discards them.
│
*)

(*       M ⊆ Sλ ∧ InternalInclusionViaCoding ∧ CodingInternalAccuracy ∧       *)
(*  DiagonalEliminator ∧ ChiEqMInternal(M, Γ, χ_eq) ∧ M ⊬_Γ ⊥ ⇒ M ⊬_Γ ¬χ_eq.  *)

Theorem mirror_unrefutability :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (chi_eq : DiagonalFormula)
         (code_Slambda_derives : CodingOfSLambdaDerivability),
    regulator_theory_included M Slambda ->
    InternalInclusionViaCoding M Gamma code_Slambda_derives ->
    CodingInternalAccuracy M Gamma code_Slambda_derives ->
    DiagonalEliminator Slambda M Gamma chi_eq ->
    ChiEqMInternal M Gamma chi_eq ->
    MirrorConsistent M Gamma ->
    ~ regulator_theory_checked_derivable M Gamma
        (formula_negation chi_eq).
Proof.
  intros Slambda M Gamma chi_eq code_Slambda_derives
    _Hincluded _Hinternal _Hsound _Hdiag HMint Hconsistent Hrefute.
  exact (mirror_unrefutability_core M Gamma chi_eq
    HMint Hconsistent Hrefute).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          SELF-EVALUATION EXCLUSION                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `self_evaluation_one_zero_excluded` excludes one
│          configuration of self-evaluation: if a formula carries
│          external standing and that standing bridges to
│          `Sλ`-derivability, the inner system cannot refute it. The
│          result requires no witness sentence and no closure
│          construction, but yields the same structural conclusion as
│          the mirror kernel — a formula the inner system is not free
│          to deny.
│
*)

(*   M ⊆ Sλ ∧ Sλ ⊬_Γ ⊥ ∧ external(φ) ∧ (external(φ) ⇒ Sλ ⊢_Γ φ) ⇒ M ⊬_Γ ¬φ.   *)

Theorem self_evaluation_one_zero_excluded :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (phi : Formula)
         (external : Formula -> Prop),
    regulator_theory_included M Slambda ->
    SLambdaConsistent Slambda Gamma ->
    external phi ->
    (external phi ->
      regulator_theory_checked_derivable Slambda Gamma phi) ->
    ~ regulator_theory_checked_derivable M Gamma
        (formula_negation phi).
Proof.
  intros Slambda M Gamma phi external
    Hincluded Hconsistent Hexternal Hbridge Hrefute.
  apply Hconsistent.
  apply regulator_theory_checked_derivable_mp_lemma with (A := phi).
  - apply regulator_theory_checked_derivable_regulator_theory_monotone_lemma
      with (R := M).
    + exact Hincluded.
    + exact Hrefute.
  - exact (Hbridge Hexternal).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            CONSTRUCTION FROM L001                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `chi_eq_m_internal_from_l001_fixed_point` derives the
│          M-side Curry property from a closure-level negation fixed
│          point. The fixed point supplies both directions of
│          equivalence between the formula and its negation; only the
│          direction needed for the Curry property is consumed.
│
*)

(*            NegFix(M ⊢_Γ ·, χ_eq) ⇒ ChiEqMInternal(M, Γ, χ_eq).             *)

Theorem chi_eq_m_internal_from_l001_fixed_point :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi_eq : DiagonalFormula),
    NegationFixedPointFor
      (regulator_theory_checked_derivable M Gamma)
      chi_eq ->
    ChiEqMInternal M Gamma chi_eq.
Proof.
  intros M Gamma chi_eq [_Hforward Hbackward] Hrefute.
  apply regulator_theory_checked_derivable_mp_lemma
    with (A := formula_negation chi_eq).
  - exact Hbackward.
  - exact Hrefute.
Qed.

(*
│
│          `l001_constructs_chi_eq_m_internal` constructs a witness
│          formula carrying the Curry property from any L001
│          evaluation frame over the inner system's derivability. The
│          witness ceases to be a free parameter of downstream
│          theorems.
│
*)

(*      ClosureEval(M ⊢_Γ ·, Code) ⇒ ∃χ_eq. ChiEqMInternal(M, Γ, χ_eq).       *)

Theorem l001_constructs_chi_eq_m_internal :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    exists chi_eq : DiagonalFormula,
      ChiEqMInternal M Gamma chi_eq.
Proof.
  intros M Gamma Code E.
  destruct
    (negfixp_existence
       (regulator_theory_checked_derivable M Gamma)
       Code
       E)
    as [chi_eq Hfixed].
  exists chi_eq.
  exact
    (chi_eq_m_internal_from_l001_fixed_point
       M Gamma chi_eq Hfixed).
Qed.

(*
│
│          `mirror_unrefutability_from_l001_evaluation` is the fully
│          discharged form: from an evaluation frame and consistency
│          alone, the theorem produces a witness sentence together
│          with the unrefutability conclusion. This is the form
│          intended for downstream consumers.
│
*)

(*         ClosureEval(M ⊢_Γ ·, Code) ∧ M ⊬_Γ ⊥ ⇒ ∃χ_eq. M ⊬_Γ ¬χ_eq.         *)

Theorem mirror_unrefutability_from_l001_evaluation :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    MirrorConsistent M Gamma ->
    exists chi_eq : DiagonalFormula,
      ~ regulator_theory_checked_derivable M Gamma
          (formula_negation chi_eq).
Proof.
  intros M Gamma Code E Hconsistent.
  destruct
    (l001_constructs_chi_eq_m_internal M Gamma Code E)
    as [chi_eq HMint].
  exists chi_eq.
  exact
    (mirror_unrefutability_core
       M Gamma chi_eq HMint Hconsistent).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            OPERATIONAL NON-ESCAPE                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `regulator_non_escape` is the operational invariant: an
│          attempted internal escape from the licensing conditions
│          cannot succeed under `Sλ`-consistency. The escape act
│          re-licenses the formula it was meant to undercut, local
│          authority converts the licensing into derivation, modus
│          ponens with the refutation collapses the inner system, and
│          inclusion transports the collapse into `Sλ` where
│          consistency forbids it.
│
*)

(*  M ⊆ Sλ ∧ Sλ ⊬_Γ ⊥ ∧ LocalAuthority(M, Γ, asif) ∧ EscapeReabsorbed(M, Γ,   *)
(*                               asif, A, e) ∧                                *)
(*                      M ⊢_Γ ¬A ∧ Escape(M, Γ, e) ⇒ ⊥.                       *)

Theorem regulator_non_escape :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (asif : AsIF)
         (A escape_claim : Formula),
    regulator_theory_included M Slambda ->
    SLambdaConsistent Slambda Gamma ->
    LocalAuthority M Gamma asif ->
    EscapeReabsorbed M Gamma asif A escape_claim ->
    regulator_theory_checked_derivable M Gamma
      (formula_negation A) ->
    Escape M Gamma escape_claim ->
    False.
Proof.
  intros Slambda M Gamma asif A escape_claim
    Hincluded Hconsistent Hauthority Hescape Hrefute Hclaim.
  apply Hconsistent.
  apply regulator_theory_checked_derivable_regulator_theory_monotone_lemma
    with (R := M).
  - exact Hincluded.
  - apply regulator_theory_checked_derivable_mp_lemma with (A := A).
    + exact Hrefute.
    + exact (Hauthority A (Hescape Hclaim)).
Qed.
