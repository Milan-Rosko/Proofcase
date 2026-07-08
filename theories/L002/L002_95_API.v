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

  Public API surface for L002. This file exports the clean-sheet
  mirror-unrefutability layer and names the package-level contracts certified
  by `L002_97_Artifacts`. Downstream packages should import this file for the
  stable premise vocabulary, theorem, and contract propositions.

  The API keeps the core mirror and self-evaluation theorems M001-native,
  then adds a separate L001-backed construction layer that discharges the
  M-side Curry hypothesis from closure evaluation, followed by the
  operational non-escape, recursive-approximation, concrete model-pattern,
  and symbolic-regulator-principle invariants. The primary explanatory
  surface is authority (`AsIF`), not M/Sλ equivalence. Rocq is the ambient
  proof theory `T`; `Sλ` is the object-level symbolic regulator represented
  by `RegulatorTheory`.

*)

From L002 Require Export L002_04__Concrete_Model_Pattern.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               PUBLIC CONTRACT                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Contract proposition for the proof-minimal kernel. Under
│          only the M-side Curry property and M-consistency, the
│          internal model `M` cannot checked-derive the negation of
│          `chi_eq`.
│
*)

Definition MIRROR_UNREFUTABILITY_CORE_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi_eq : DiagonalFormula),
    ChiEqMInternal M Gamma chi_eq ->
    MirrorConsistent M Gamma ->
    ~ regulator_theory_checked_derivable M Gamma
        (formula_negation chi_eq).

(*
│
│          Contract proposition for the retained full-interface
│          milestone theorem. The `Sλ`-side mirror data is documentary
│          compatibility surface; the load-bearing
│          authority/non-escape content remains the M-side Curry
│          property plus consistency.
│
*)

Definition MIRROR_UNREFUTABILITY_CONTRACT : Prop :=
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

(*
│
│          Contract proposition for the self-evaluation one-zero
│          exclusion theorem. If external status for `phi` bridges to
│          `Sλ`-checked derivability, then an included internal
│          regulator `M` cannot checked-refute `phi` under
│          `Sλ`-consistency.
│
*)

Definition SELF_EVALUATION_ONE_ZERO_EXCLUDED_CONTRACT : Prop :=
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

(*
│
│          Contract proposition for the L001-to-L002 projection step.
│          A closure-level negation fixed point at M-checked
│          derivability yields the M-side Curry property required by
│          the mirror-unrefutability kernel.
│
*)

Definition CHI_EQ_M_INTERNAL_FROM_L001_FIXED_POINT_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (chi_eq : DiagonalFormula),
    NegationFixedPointFor
      (regulator_theory_checked_derivable M Gamma)
      chi_eq ->
    ChiEqMInternal M Gamma chi_eq.

(*
│
│          Contract proposition for constructing an M-side Curry
│          witness from L001 evaluation closure. The constructed
│          formula is existential: the contract no longer asks the
│          caller to supply `chi_eq` or `ChiEqMInternal`.
│
*)

Definition L001_CONSTRUCTS_CHI_EQ_M_INTERNAL_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    exists chi_eq : DiagonalFormula,
      ChiEqMInternal M Gamma chi_eq.

(*
│
│          Contract proposition for the constructed
│          mirror-unrefutability endpoint. L001 evaluation closure
│          supplies the diagonal, and M-consistency supplies the final
│          obstruction to M-checked refutation.
│
*)

Definition MIRROR_UNREFUTABILITY_FROM_L001_EVALUATION_CONTRACT : Prop :=
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

(*
│
│          Contract proposition for the operational non-escape
│          invariant. A checked escape claim that reactivates local
│          authority for `A`, together with an M-checked refutation of
│          `A`, destabilizes `Sλ` under M-into-Sλ inclusion and
│          `Sλ`-consistency.
│
*)

Definition REGULATOR_NON_ESCAPE_CONTRACT : Prop :=
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

(*
│
│          Contract proposition for the abstract-model non-escape
│          invariant. The local contradiction is produced inside an
│          arbitrary embedded model through explicit local MP and
│          authority interfaces, then transported to the enclosing
│          regulator.
│
*)

Definition MODEL_REGULATOR_NON_ESCAPE_CONTRACT : Prop :=
  forall (Model : Type)
         (Slambda : RegulatorTheory)
         (Gamma : Context)
         (derives : ModelDerivability Model)
         (asif : AsIFFor Model)
         (m : Model)
         (A escape_claim : Formula),
    ModelEmbeddedInRegulator Model Slambda Gamma derives ->
    SLambdaConsistent Slambda Gamma ->
    ModelModusPonens Model derives ->
    ModelLocalAuthority Model derives asif ->
    ModelEscapeReabsorbed Model derives asif m A escape_claim ->
    derives m (formula_negation A) ->
    derives m escape_claim ->
    False.

(*
│
│          Contract proposition for the formal unifying invariant:
│          authority internalizes locally, transports through
│          embedding, and stable continuation supplies bounded
│          recursive pressure.
│
*)

Definition EMBEDDED_AUTHORITY_STABILITY_LIMIT_CONTRACT : Prop :=
  forall (Model : Type)
         (Slambda : RegulatorTheory)
         (Gamma : Context)
         (derives : ModelDerivability Model)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (m : Model)
         (A : Formula),
    ModelEmbeddedInRegulator Model Slambda Gamma derives ->
    ModelLocalAuthority Model derives asif ->
    StableRequiresBoundedRecursivePressure Model R ->
    asif m A ->
    Stable R m ->
    derives m A /\
    regulator_theory_checked_derivable Slambda Gamma A /\
    exists bound : nat,
      BoundedIntrospection Model R bound m.

(*
│
│          Contract proposition for the formal "mistake" reading.
│          Local authority plus a counter-certification attempt
│          produces local derivability and nested recursive pressure,
│          not a semantic falsity claim.
│
*)

Definition LOCAL_AUTHORITY_COUNTER_CERTIFICATION_YIELDS_RECURSIVE_PRESSURE_CONTRACT
    : Prop :=
  forall (Model : Type)
         (derives : ModelDerivability Model)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (depth : nat)
         (m : Model)
         (A : Formula),
    ModelLocalAuthority Model derives asif ->
    RecursiveDepthPositivePenalty Model R ->
    asif m A ->
    CounterCertificationAt Model R depth m A ->
    derives m A /\
    NestedAuthorityPressure Model asif R depth m A.

(*
│
│          Contract proposition for the finite-depth nested pressure
│          step. A witnessed nested authority/counter-approximation
│          configuration strictly increases depth-indexed pressure
│          under the caller-supplied authority-depth pressure law.
│
*)

Definition NESTED_AUTHORITY_PRESSURE_INCREASES_PENALTY_AT_DEPTH_CONTRACT
    : Prop :=
  forall (Model : Type)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (depth : nat)
         (m : Model)
         (A : Formula),
    RecursiveAuthorityDepthPressure Model asif R ->
    NestedAuthorityPressure Model asif R depth m A ->
    PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m.

(*
│
│          Contract proposition for strict depth-growth producing
│          unbounded recursive pressure.
│
*)

Definition STRICT_DEPTH_PRESSURE_UNBOUNDED_CONTRACT : Prop :=
  forall (Model : Type)
         (R : RecursiveApproximationStructure Model)
         (m : Model),
    (forall depth : nat,
       PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m) ->
    UnboundedRecursivePressure Model R m.

(*
│
│          Contract proposition for the unbounded-depth obstruction.
│          Strict pressure growth at every depth rules out stable
│          continuation under the bounded-pressure stability
│          principle.
│
*)

Definition STRICT_DEPTH_PRESSURE_OBSTRUCTS_STABILITY_CONTRACT : Prop :=
  forall (Model : Type)
         (R : RecursiveApproximationStructure Model)
         (m : Model),
    StableRequiresBoundedRecursivePressure Model R ->
    (forall depth : nat,
       PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m) ->
    ~ Stable R m.

(*
│
│          Contract proposition for the authority-specific
│          obstruction. Nested authority pressure at every depth rules
│          out stable continuation when the authority-depth pressure
│          law turns each witness into a strict pressure increase.
│
*)

Definition NESTED_AUTHORITY_PRESSURE_OBSTRUCTS_STABILITY_CONTRACT : Prop :=
  forall (Model : Type)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (m : Model)
         (A : Formula),
    RecursiveAuthorityDepthPressure Model asif R ->
    (forall depth : nat,
       NestedAuthorityPressure Model asif R depth m A) ->
    StableRequiresBoundedRecursivePressure Model R ->
    ~ Stable R m.

(*
│
│          Contract proposition for the concrete reusable model
│          pattern. This pins the one-state
│          authority/counter-approximation instance and its bridge
│          laws as part of the public package boundary.
│
*)

Definition CONCRETE_MODEL_PATTERN_CONTRACT : Prop :=
  CONCRETE_MODEL_PATTERN.

(*
│
│          Contract proposition for the L002_03 construction endpoint.
│          From any L001 evaluation frame at `M`-checked derivability
│          and M-consistency, the embedded subsystem has an
│          undecidable formula.
│
*)

Definition EVALUATION_FRAME_YIELDS_UNDECIDABLE_IN_M_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    MirrorConsistent M Gamma ->
    exists B : Formula, Undecidable M Gamma B.

(*
│
│          Contract proposition for Principle 1. A consistent embedded
│          subsystem with an evaluation frame has a formula it does
│          not checked-derive.
│
*)

Definition ENABLEMENT_OF_FALSEHOODS_CONTRACT : Prop :=
  forall (M : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable M Gamma)
                Code),
    MirrorConsistent M Gamma ->
    exists Phi : Formula,
      ~ regulator_theory_checked_derivable M Gamma Phi.

(*
│
│          Contract proposition for Principle 2. An L001-backed
│          undecidable formula can be paired with a caller-supplied
│          admissibility witness for its undecidability claim.
│
*)

Definition PARADOX_OF_THE_EXTERNAL_CONTRACT : Prop :=
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

(*
│
│          Contract proposition for Principle 3. A consistent `Sλ`
│          with an evaluation frame has a formula it does not
│          checked-derive.
│
*)

Definition PERPETUITY_OF_IGNORANCE_CONTRACT : Prop :=
  forall (Slambda : RegulatorTheory)
         (Gamma : Context)
         Code
         (E : ClosureEvaluationFrame
                (regulator_theory_checked_derivable Slambda Gamma)
                Code),
    SLambdaConsistent Slambda Gamma ->
    exists phi : Formula,
      ~ regulator_theory_checked_derivable Slambda Gamma phi.

(*
│
│          Contract proposition for Principle 5. The embedded
│          subsystem cannot checked-derive a perfect-certainty
│          representative while still operating under a supplied trust
│          admissibility surface.
│
*)

Definition IMPOSSIBILITY_OF_PERFECT_DOUBT_CONTRACT : Prop :=
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

(*
│
│          Contract proposition for Principle 7. Given an explicit
│          M/Sλ incompleteness witness, a consistent embedded
│          subsystem with an evaluation frame preserves that
│          incompleteness and has a success representative it does not
│          checked-derive.
│
*)

Definition INCOMPREHENSIBILITY_OF_SYMBOLIC_REGULATION_CONTRACT : Prop :=
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

(*
│
│          Bundled contract for the public L002_03
│          symbolic-regulator-principle endpoints.
│
*)

Definition SYMBOLIC_REGULATOR_PRINCIPLES_CONTRACT : Prop :=
  EVALUATION_FRAME_YIELDS_UNDECIDABLE_IN_M_CONTRACT /\
  ENABLEMENT_OF_FALSEHOODS_CONTRACT /\
  PARADOX_OF_THE_EXTERNAL_CONTRACT /\
  PERPETUITY_OF_IGNORANCE_CONTRACT /\
  IMPOSSIBILITY_OF_PERFECT_DOUBT_CONTRACT /\
  INCOMPREHENSIBILITY_OF_SYMBOLIC_REGULATION_CONTRACT.

(*
│
│          Complete L002 package contract. The package exposes the
│          mirror-unrefutability core, the full-interface wrapper, the
│          self-evaluation one-zero exclusion endpoint, the
│          L001-backed construction that discharges the M-side Curry
│          hypothesis, the operational non-escape invariant, the
│          unifying embedded-authority stability invariant, the
│          concrete model-pattern witness, and the
│          symbolic-regulator-principle endpoints.
│
*)

Definition SYMBOLIC_REGULATION_CONTRACT : Prop :=
  MIRROR_UNREFUTABILITY_CORE_CONTRACT /\
  MIRROR_UNREFUTABILITY_CONTRACT /\
  SELF_EVALUATION_ONE_ZERO_EXCLUDED_CONTRACT /\
  CHI_EQ_M_INTERNAL_FROM_L001_FIXED_POINT_CONTRACT /\
  L001_CONSTRUCTS_CHI_EQ_M_INTERNAL_CONTRACT /\
  MIRROR_UNREFUTABILITY_FROM_L001_EVALUATION_CONTRACT /\
  REGULATOR_NON_ESCAPE_CONTRACT /\
  MODEL_REGULATOR_NON_ESCAPE_CONTRACT /\
  EMBEDDED_AUTHORITY_STABILITY_LIMIT_CONTRACT /\
  LOCAL_AUTHORITY_COUNTER_CERTIFICATION_YIELDS_RECURSIVE_PRESSURE_CONTRACT /\
  NESTED_AUTHORITY_PRESSURE_INCREASES_PENALTY_AT_DEPTH_CONTRACT /\
  STRICT_DEPTH_PRESSURE_UNBOUNDED_CONTRACT /\
  STRICT_DEPTH_PRESSURE_OBSTRUCTS_STABILITY_CONTRACT /\
  NESTED_AUTHORITY_PRESSURE_OBSTRUCTS_STABILITY_CONTRACT /\
  CONCRETE_MODEL_PATTERN_CONTRACT /\
  SYMBOLIC_REGULATOR_PRINCIPLES_CONTRACT.

(*
│
│          Named package witness certified by
│          `symbolic_regulation_qed` in `L002_97_Artifacts`.
│
*)

Definition WITNESS : Prop :=
  SYMBOLIC_REGULATION_CONTRACT.
