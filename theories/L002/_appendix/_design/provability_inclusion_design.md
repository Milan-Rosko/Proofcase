# L002 Provability Inclusion Design

## §1 - Recap

The prose theorem 2.3.6, Provability Inclusion, says that a symbolic
regulator has a limitation around internally certified correctness of its
own symbolic subcomponents. Point 1 says that there is a formula phi
which is true in the ambient metatheory V, while the internal model M
cannot prove that any definable subcomponent correctly handles phi.
Point 2 says that, for a phi of that kind, the regulator cannot
internally refute the claim that a specific subcomponent is incorrect
with respect to phi, even though that subcomponent is correct from the
external point of view. Point 3 says that no symbolic regulator can
internally prove one global statement asserting that all of its symbolic
subcomponents are correct across all formulas. The L002 design must
translate this into M001 checked-derivability vocabulary without adding
semantic truth, arithmetized Bew, HBL machinery, or classical soundness
assumptions.

## §2 - Design Call 1 Resolution

Chosen option: 1A - Sλ-derivability. The replacement for "phi is true in
V" will be `regulator_theory_checked_derivable Slambda Gamma phi`, where
`Slambda` names `Sλ`, the object-level symbolic regulator theory. This is
the only option that gives L002 a
real syntactic theorem shape without smuggling a semantic truth predicate
or introducing a soundness principle that the package has so far refused.
The cost is explicit: the theorem will not say "true in the external
universe" in the semantic sense; it will say "committed to by the outer
checked-derivability layer." A concrete formula satisfying the
replacement is any `phi0 : Formula` for which a consumer supplies
`regulator_theory_checked_derivable Slambda Gamma phi0`, for example a formula
already present in `Gamma` or available as a Sλ-axiom under the relevant
M001 profile. A concrete formula not satisfying the replacement, under a
consistent nontrivial Sλ, would be `Bot` when no checked proof of `Bot`
from `Gamma` exists in Sλ.

## §3 - Design Call 2 Resolution

Chosen option: 2A - Pi-quantified parameter `Subcomponent : Type`. The
subcomponent layer should remain a theorem parameter at this stage,
because the current L002 theorem layer is intentionally M001-native and
does not yet commit to a concrete representation of axioms, rules, or
modules. This is the same discipline used for `CodingOfSLambdaDerivability`
and `DiagonalFormula`: expose the missing structure honestly, require
the consumer to instantiate it, and avoid prematurely dragging M001's
logic-profile internals into L002. A downstream Point 2 proof discharges
"for some C_i" by taking a named parameter `Ci : Subcomponent` together
with the required correctness and Curry hypotheses for that component;
the proof then uses `exists Ci`. If a consumer chooses a concrete
subcomponent type later, such as a finite enumeration of internal
modules, `Ci` becomes one constructor or named element of that type.

## §4 - Design Call 3 Resolution

Chosen option: 3B - three separate theorems. The three prose Points
share vocabulary, but they do not have the same proof obligations:
Point 1 is an existence result around a supplied or constructed witness
formula, Point 2 is a component-specific non-refutability theorem at a
chosen witness, and Point 3 is a global non-derivability result for an
object-level all-correctness representative. Splitting them keeps each
load-bearing structure visible and gives each Point its own contract and
assumption report. This also supports the likely refinement path: Point
1 and Point 2 can initially be witness-parameterized, while Point 3 can
be refined independently once the object-language representative of
global correctness is settled.

## §5 - Resulting Theorem Shape

The following is a Coq-style sketch only. It is not intended to compile
as written, but it fixes the vocabulary and hypothesis shape for a later
Coq implementation.

```coq
(* Subcomponents are supplied by the consumer. *)
Variable Subcomponent : Type.

(* Correct C phi is an object-language formula saying that
   subcomponent C correctly handles phi. *)
Variable Correct : Subcomponent -> Formula -> Formula.

(* ActsAsIf M Gamma psi means M cannot checked-derive the
   object-level negation of psi. *)
Definition ActsAsIf
    (M : RegulatorTheory)
    (Gamma : Context)
    (psi : Formula) : Prop :=
  ~ regulator_theory_checked_derivable M Gamma
      (formula_negation psi).

(* Point-1 witness shape: phi is visible at Sλ,
   but M cannot certify correctness of any subcomponent at phi. *)
Definition ProvabilityInclusionWitness
    (Slambda M : RegulatorTheory)
    (Gamma : Context)
    (Correct : Subcomponent -> Formula -> Formula)
    (phi : Formula) : Prop :=
  regulator_theory_checked_derivable Slambda Gamma phi /\
  forall C : Subcomponent,
    ~ regulator_theory_checked_derivable M Gamma
        (Correct C phi).

Theorem provability_inclusion_point1 :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (Correct : Subcomponent -> Formula -> Formula)
         (phi : Formula),
    regulator_theory_checked_derivable Slambda Gamma phi ->
    (forall C : Subcomponent,
       ~ regulator_theory_checked_derivable M Gamma
           (Correct C phi)) ->
    exists psi : Formula,
      ProvabilityInclusionWitness Slambda M Gamma Correct psi.

(* The claim that C is incorrect at phi is represented by
   formula_negation (Correct C phi). To act as if that claim is live,
   M must fail to refute it, i.e. fail to derive its negation. *)
Definition IncorrectClaim
    (Correct : Subcomponent -> Formula -> Formula)
    (C : Subcomponent)
    (phi : Formula) : Formula :=
  formula_negation (Correct C phi).

Definition IncorrectClaimCurry
    (M : RegulatorTheory)
    (Gamma : Context)
    (Correct : Subcomponent -> Formula -> Formula)
    (C : Subcomponent)
    (phi : Formula) : Prop :=
  regulator_theory_checked_derivable M Gamma
    (formula_negation (IncorrectClaim Correct C phi)) ->
  regulator_theory_checked_derivable M Gamma
    (IncorrectClaim Correct C phi).

Theorem provability_inclusion_point2 :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (Correct : Subcomponent -> Formula -> Formula)
         (phi : Formula)
         (Ci : Subcomponent),
    ProvabilityInclusionWitness Slambda M Gamma Correct phi ->
    regulator_theory_checked_derivable Slambda Gamma
      (Correct Ci phi) ->
    IncorrectClaimCurry M Gamma Correct Ci phi ->
    MirrorConsistent M Gamma ->
    exists C : Subcomponent,
      regulator_theory_checked_derivable Slambda Gamma
        (Correct C phi) /\
      ActsAsIf M Gamma
        (IncorrectClaim Correct C phi).

(* M001 has no native object-language universal quantifier. The
   all-correctness claim is therefore represented by a supplied
   Formula, together with an eliminator explaining what M-deriving
   that Formula gives. *)
Definition GlobalCorrectnessEliminator
    (M : RegulatorTheory)
    (Gamma : Context)
    (Correct : Subcomponent -> Formula -> Formula)
    (all_correct : Formula) : Prop :=
  regulator_theory_checked_derivable M Gamma all_correct ->
  forall (phi : Formula) (C : Subcomponent),
    regulator_theory_checked_derivable M Gamma
      (Correct C phi).

Theorem provability_inclusion_point3 :
  forall (M : RegulatorTheory)
         (Gamma : Context)
         (Correct : Subcomponent -> Formula -> Formula)
         (all_correct : Formula)
         (phi_bad : Formula)
         (C_bad : Subcomponent),
    GlobalCorrectnessEliminator M Gamma Correct all_correct ->
    ~ regulator_theory_checked_derivable M Gamma
        (Correct C_bad phi_bad) ->
    ~ regulator_theory_checked_derivable M Gamma all_correct.

(* Optional bundled naming layer, not the primary theorem shape:
   the three separate theorems may later be collected into a contract
   proposition if the individual endpoints are stable. *)
Definition PROVABILITY_INCLUSION_CONTRACT : Prop :=
  (* Point 1 contract *) True /\
  (* Point 2 contract *) True /\
  (* Point 3 contract *) True.
```

The sketch intentionally exposes the witness assumptions for Point 1 and
Point 2 rather than pretending that L002 can currently construct the
formula phi or the component Ci. The existence conclusions are therefore
honest witness-packaging results at this stage, with construction left
to later refinement.

## §6 - Refinement Targets

- `Subcomponent : Type` - Discharge by choosing a concrete representation
  of symbolic subcomponents, such as a finite module enumeration or a
  structured view of M001 axioms and rule-profile entries.

- `Correct : Subcomponent -> Formula -> Formula` - Discharge by building
  object-language correctness formulas for the chosen subcomponent
  representation.

- `phi : Formula` for Point 1 - Discharge by constructing a checked
  derivability gap witness, most likely from the same evaluation-closure
  work that will eventually construct mirror diagonals.

- `Ci : Subcomponent` for Point 2 - Discharge by naming a concrete
  subcomponent in the selected subcomponent representation.

- `IncorrectClaimCurry` - Discharge by constructing a Curry-style
  representative for the incorrectness claim at the chosen component and
  formula.

- `all_correct : Formula` - Discharge by constructing an object-language
  representative of the global correctness claim for the selected
  subcomponent universe.

- `GlobalCorrectnessEliminator` - Discharge by proving that M-derivability
  of `all_correct` yields M-derivability of each component correctness
  instance.

- `regulator_theory_checked_derivable Slambda Gamma phi` - Discharge by an
  explicit checked proof in `Sλ` or by a construction that
  produces a Sλ-derivable witness formula.

## §7 - Risks

- Option 1A is syntactic, not semantic: the resulting theorem talks about
  Sλ-checked commitments, not truth in an external universe V.

- Option 2A leaves `Subcomponent` completely unconstrained; a consumer can
  instantiate it with a type that has little connection to actual M001
  axioms, rules, or modules.

- Point 1 is witness-driven at Stage 0. If the witness formula is supplied
  directly, the proof may look like existential packaging rather than a
  substantive construction until the refinement stage constructs phi.

- Point 2 requires an inhabited subcomponent type through the named
  parameter `Ci : Subcomponent`. Without such a parameter, an existential
  over an arbitrary `Subcomponent : Type` would not be derivable.

- The object-language phrase "forall C forall phi, Correct C phi" is not
  native to M001. Any Point 3 implementation needs a supplied
  `all_correct : Formula` plus an eliminator, or else it silently assumes
  object-language quantification that M001 does not have.

- The `IncorrectClaimCurry` hypothesis is powerful. If it is not later
  discharged by a real fixed-point construction, Point 2 will remain a
  parameter-interface theorem rather than a constructed mirror result.

- If a later implementation chooses Option 2B instead, it may require
  exposing M001 logic-profile internals in L002_00, making the dependency
  surface heavier than the current clean M001_95_API import.
