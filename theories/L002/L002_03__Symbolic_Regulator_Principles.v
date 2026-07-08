(*L002_03__Symbolic_Regulator_Principles.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│              Proofcase / L002_03__Symbolic_Regulator_Principles              │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We collect five structural principles governing the relationship between an
  embedded subsystem and `Sλ`. Each principle's load-bearing non-derivability
  fact is discharged through the L001 evaluation-closure machinery: a
  closure-level negation fixed point at the embedded subsystem's checked
  derivability produces a formula that is genuinely undecidable in `M` under
  `MirrorConsistent`. That formula plays the role of the soundness sentence
  in Principle 1, the universal-trust sentence in Principle 5, and the
  agent-success sentence in Principle 7. The classical setting derives the
  same non-derivability facts from Gödel's second incompleteness theorem; the
  construction here is constructive and does not appeal to that machinery.

  The file omits two further principles. The first, on per-component blind
  spots, requires a first-class carrier for components of the regulator and
  is therefore out of the current vocabulary. The second, on nested mirror
  hierarchies, belongs in the abstract-model layer of `L002_02` where
  multi-model nesting is already available. Each principle below takes an
  L001 evaluation frame as an explicit hypothesis; downstream callers supply
  the frame through any concrete model of `M`-checked derivability.

*)

From L002 Require Export L002_02__Recursive_Approximation.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             AUXILIARY VOCABULARY                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `Undecidable M Γ φ` records that the embedded subsystem `M`
│          neither checked-derives `φ` nor checked-refutes it at the
│          working context. The predicate is symmetric and
│          constructive; it does not claim either branch is true
│          outside `M`.
│
*)

(*                 Undecidable(M, Γ, φ) ≔ M ⊬_Γ φ ∧ M ⊬_Γ ¬φ.                 *)

Definition Undecidable
    (M : RegulatorTheory)
    (Gamma : Context)
    (phi : Formula) : Prop :=
  ~ regulator_theory_checked_derivable M Gamma phi /\
  ~ regulator_theory_checked_derivable M Gamma (formula_negation phi).

(*
│
│          `SLambdaIncomplete M Slambda Γ` records that the embedded
│          subsystem's theory differs from `Sλ` at the working
│          context: some formula is `Sλ`-derivable but not
│          `M`-derivable. This is the M001-native counterpart of
│          `Th(M(Sλ)) ≠ Th(Sλ)`.
│
*)

(*           SLambdaIncomplete(M, Sλ, Γ) ≔ ∃φ. Sλ ⊢_Γ φ ∧ M ⊬_Γ φ.            *)

Definition SLambdaIncomplete
    (M Slambda : RegulatorTheory)
    (Gamma : Context) : Prop :=
  exists phi : Formula,
    regulator_theory_checked_derivable Slambda Gamma phi /\
    ~ regulator_theory_checked_derivable M Gamma phi.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                      CHECKED DERIVABILITY AS A CLOSURE                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `checked_derivability_closure_modus_ponens` exposes the
│          M001 modus-ponens lemma as the closure-level modus-ponens
│          condition for `M`-checked derivability. It is the bridge
│          that lets the L001 obstruction theorems consume checked
│          derivability as their ambient closure predicate.
│
*)

(*                        ClosureModusPonens(M ⊢_Γ ·).                        *)

Lemma checked_derivability_closure_modus_ponens :
  forall (M : RegulatorTheory) (Gamma : Context),
    ClosureModusPonens (regulator_theory_checked_derivable M Gamma).
Proof.
  intros M Gamma A B Himp Harg.
  exact (regulator_theory_checked_derivable_mp_lemma M Gamma A B Himp Harg).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             UNDECIDABILITY IN M                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `negfixp_yields_undecidable_in_m` is the central
│          construction of the file. A closure-level negation fixed
│          point at `M`-checked derivability — that is, a formula `B`
│          with `M ⊢_Γ B ⇔ M ⊢_Γ ¬B` — is undecidable in `M` whenever
│          `M` is consistent. If `M` derived either branch, the
│          closure equivalence would transport the derivation across
│          negation and M001 modus ponens would collapse `M` to
│          bottom, contradicting consistency.
│
*)

(*    NegFix(M ⊢_Γ ·, B) ∧ MirrorConsistent(M, Γ) ⇒ Undecidable(M, Γ, B).     *)

Lemma negfixp_yields_undecidable_in_m :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (B : Formula),
    NegationFixedPointFor (regulator_theory_checked_derivable M Gamma) B ->
    MirrorConsistent M Gamma ->
    Undecidable M Gamma B.
Proof.
  intros M Gamma B [Hforward Hbackward] Hconsistent.
  split.
  - intro HB.
    apply Hconsistent.
    apply regulator_theory_checked_derivable_mp_lemma
      with (A := B).
    + apply regulator_theory_checked_derivable_mp_lemma
        with (A := B).
      * exact Hforward.
      * exact HB.
    + exact HB.
  - intro HnegB.
    apply Hconsistent.
    apply regulator_theory_checked_derivable_mp_lemma
      with (A := B).
    + exact HnegB.
    + apply regulator_theory_checked_derivable_mp_lemma
        with (A := formula_negation B).
      * exact Hbackward.
      * exact HnegB.
Qed.

(*
│
│          `evaluation_frame_yields_undecidable_in_m` packages the
│          construction at the evaluation-frame level. From any L001
│          evaluation frame at `M`-checked derivability and
│          consistency of `M`, the theorem returns an explicit formula
│          undecidable in `M`. This is the witness that downstream
│          principles use as the soundness, trust, and success
│          sentence.
│
*)

(*ClosureEval(M ⊢_Γ ·, Code) ∧ MirrorConsistent(M, Γ) ⇒ ∃B. Undecidable(M, Γ, *)
(*                                    B).                                     *)

Theorem evaluation_frame_yields_undecidable_in_m :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    MirrorConsistent M Gamma ->
    exists B : Formula, Undecidable M Gamma B.
Proof.
  intros M Gamma Code E Hconsistent.
  destruct
    (negfixp_existence
       (regulator_theory_checked_derivable M Gamma)
       Code E)
    as [B Hfixed].
  exists B.
  exact (negfixp_yields_undecidable_in_m M Gamma B Hfixed Hconsistent).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           ENABLEMENT OF FALSEHOODS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `enablement_of_falsehoods` records that the embedded
│          subsystem does not internally derive its own soundness
│          sentence. The soundness role is filled here by a formula
│          constructed as a negation fixed point at `M`-checked
│          derivability, which `negfixp_yields_undecidable_in_m` shows
│          is non-derivable in `M` under consistency. The principle
│          returns this witness together with the non-derivability
│          fact. Read in the regulator picture, no consistent embedded
│          subsystem capable of evaluation-closure construction proves
│          its own global soundness, leaving open the operational
│          possibility of unsound internal moves.
│
*)

(*   ClosureEval(M ⊢_Γ ·, Code) ∧ MirrorConsistent(M, Γ) ⇒ ∃Phi. M ⊬_Γ Phi.   *)

Theorem enablement_of_falsehoods :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    MirrorConsistent M Gamma ->
    exists Phi : Formula,
      ~ regulator_theory_checked_derivable M Gamma Phi.
Proof.
  intros M Gamma Code E Hconsistent.
  destruct
    (evaluation_frame_yields_undecidable_in_m M Gamma Code E Hconsistent)
    as [Phi [HnotPhi _]].
  exists Phi.
  exact HnotPhi.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           PARADOX OF THE EXTERNAL                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `paradox_of_the_external` records the existence of an
│          undecidable formula whose undecidability the regulator
│          licenses. The undecidability witness comes from the L001
│          construction; the licensing surface is supplied by the
│          caller through a function `undec_witness` representing,
│          inside `M`, the meta-claim of undecidability for a given
│          formula. The theorem additionally asks the caller to commit
│          the licensing surface to those witness formulas uniformly.
│          Read in the regulator picture, the embedded subsystem must
│          treat its own undecidabilities as externally licensed even
│          though it cannot internally decide them.
│
*)

(*         ClosureEval(M ⊢_Γ ·, Code) ∧ MirrorConsistent(M, Γ) ∧ (∀φ.         *)
(*                         asif(undec_witness(φ))) ⇒                          *)
(*             ∃φ. Undecidable(M, Γ, φ) ∧ asif(undec_witness(φ)).             *)

Theorem paradox_of_the_external :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (asif : AsIF)
         (undec_witness : Formula -> Formula)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    MirrorConsistent M Gamma ->
    (forall phi : Formula, asif (undec_witness phi)) ->
    exists phi : Formula,
      Undecidable M Gamma phi /\ asif (undec_witness phi).
Proof.
  intros M Gamma asif undec_witness Code E Hconsistent Hasif.
  destruct
    (evaluation_frame_yields_undecidable_in_m M Gamma Code E Hconsistent)
    as [phi Hundec].
  exists phi.
  split.
  - exact Hundec.
  - exact (Hasif phi).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           PERPETUITY OF IGNORANCE                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `perpetuity_of_ignorance` records the existence of a
│          formula that `Sλ` does not derive. The L001 construction is
│          applied at `Sλ`'s checked derivability rather than `M`'s;
│          the resulting formula is undecidable in `Sλ` under
│          `SLambdaConsistent Slambda Γ`. Read in the regulator
│          picture, even the consistent symbolic regulator carries
│          formulas it cannot decide, so the embedded subsystem
│          inherits not just its own incompleteness but the
│          incompleteness of the system regulating it.
│
*)

(*   ClosureEval(Sλ ⊢_Γ ·, Code) ∧ SLambdaConsistent(Sλ, Γ) ⇒ ∃φ. Sλ ⊬_Γ φ.   *)

Theorem perpetuity_of_ignorance :
  forall (Slambda : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable Slambda Gamma)
                Code),
    SLambdaConsistent Slambda Gamma ->
    exists phi : Formula,
      ~ regulator_theory_checked_derivable Slambda Gamma phi.
Proof.
  intros Slambda Gamma Code E Hconsistent.
  destruct
    (negfixp_existence
       (regulator_theory_checked_derivable Slambda Gamma)
       Code E)
    as [phi Hfixed].
  exists phi.
  destruct
    (negfixp_yields_undecidable_in_m Slambda Gamma phi Hfixed Hconsistent)
    as [Hnotphi _].
  exact Hnotphi.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        IMPOSSIBILITY OF PERFECT DOUBT                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `impossibility_of_perfect_doubt` records that the embedded
│          subsystem does not internally derive a universal-soundness
│          sentence, while operating under licensing of a separate
│          existential-trust sentence. The non-derivability of
│          `perfect` is discharged through the L001 construction; the
│          licensing of `trust` is supplied by the caller through the
│          existing `AsIF` surface. Read in the regulator picture, the
│          subsystem cannot justify the claim that every one of its
│          components is sound for every formula, but it must operate
│          as though at least one of them is — a structural commitment
│          to trust at the cost of certainty.
│
*)

(*    ClosureEval(M ⊢_Γ ·, Code) ∧ MirrorConsistent(M, Γ) ∧ asif(trust) ⇒     *)
(*                   ∃perfect. M ⊬_Γ perfect ∧ asif(trust).                   *)

Theorem impossibility_of_perfect_doubt :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (asif : AsIF)
         (trust : Formula)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    MirrorConsistent M Gamma ->
    asif trust ->
    exists perfect : Formula,
      ~ regulator_theory_checked_derivable M Gamma perfect /\ asif trust.
Proof.
  intros M Gamma asif trust Code E Hconsistent Htrust.
  destruct
    (evaluation_frame_yields_undecidable_in_m M Gamma Code E Hconsistent)
    as [perfect [Hnotperfect _]].
  exists perfect.
  split.
  - exact Hnotperfect.
  - exact Htrust.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                  INCOMPREHENSIBILITY OF SYMBOLIC REGULATION                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `incomprehensibility_of_symbolic_regulation` is the
│          two-part principle: the embedded subsystem cannot fully
│          capture `Sλ`'s theory, and no internal agent-success
│          sentence is derivable in `M`. The incompleteness half
│          (`SLambdaIncomplete M Slambda Γ`) is supplied as a
│          hypothesis, since constructing a witness separating `M` and
│          `Sλ` requires a distinguished axiom or evaluation step that
│          the package does not commit to. The non-derivability half
│          follows from the L001 construction at `M`-checked
│          derivability. Read in the regulator picture, the embedded
│          subsystem fails to grasp its own incompleteness from the
│          inside, and the formula expressing its own operational
│          success is among the formulas it cannot derive.
│
*)

(*         SLambdaIncomplete(M, Sλ, Γ) ∧ ClosureEval(M ⊢_Γ ·, Code) ∧         *)
(*                          MirrorConsistent(M, Γ) ⇒                          *)
(*           SLambdaIncomplete(M, Sλ, Γ) ∧ ∃success. M ⊬_Γ success.           *)

Theorem incomprehensibility_of_symbolic_regulation :
  forall (M Slambda : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    SLambdaIncomplete M Slambda Gamma ->
    MirrorConsistent M Gamma ->
    SLambdaIncomplete M Slambda Gamma /\
    exists success : Formula,
      ~ regulator_theory_checked_derivable M Gamma success.
Proof.
  intros M Slambda Gamma Code E Hincomplete Hconsistent.
  split.
  - exact Hincomplete.
  - destruct
      (evaluation_frame_yields_undecidable_in_m M Gamma Code E Hconsistent)
      as [success [Hnotsuccess _]].
    exists success.
    exact Hnotsuccess.
Qed.
