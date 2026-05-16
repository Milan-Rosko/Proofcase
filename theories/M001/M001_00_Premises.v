(*M001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / M001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  CONSTRUCTIVE REGULATOR THEORY is a finite, syntactic, object theory for
  regulators governed by symbolic logic. Above this premise file we develop a
  closed implicational/falsity object language, finite proof scripts with
  first-class instructions, a total Boolean checker, executable deduction and
  constructive-reductio transformers, certified MP composition, syntactic
  adequacy of checked and inductive derivability, negative precomposition,
  the symbolic-regulator presentation, and the checker/regulator unfolding
  theorems that connect the regulator vocabulary back to
  `regulator_theory_check_bool`. Everything M001 ships is operational in this
  sense; semantic interpretation, model theory, and modal provability are
  explicitly outside the package.

  The trusted base of M001 is intentionally narrow. We import only
  `Bool.Bool`, `Lists.List`, and `Arith_base` from the standard library, and
  we open `ListNotations` so that finite proof scripts read cleanly
  throughout. No further base is needed: the checker is a Boolean function on
  finite lists of natural-number-indexed proof lines, the deduction
  transformer is a structural recursion on the same data, and the certificate
  verifiers are point-free Boolean conjunctions. We deliberately avoid
  classical logic libraries, real numbers, set-theoretic libraries,
  extraction or IO protocol modules, semantic truth, model theory,
  arithmetized syntax, object-level substitution, self-tokens, and internal
  self-interpretation principles; every one of those would either widen the
  trust boundary or commit the package to an interpretation it does not have.

*)

(*
│
│          `Bool.Bool` supplies the Boolean checker codomain and the
│          `if` `andb` `orb` algebra used throughout.
│
*)

From Stdlib Require Export Bool.Bool.

(*
│
│          `Lists.List` supplies the carrier for contexts, finite
│          axiom sets, proof scripts, and regulator components.
│
*)

From Stdlib Require Export Lists.List.

(*
│
│          `Arith_base` supplies the natural-number indexing used by
│          `mp_valid_bool`, the deduction transformer's index map, and
│          every `nth`-style accessor.
│
*)

From Stdlib Require Export Arith_base.

(*
│
│          `ListNotations` is opened as a notation scope, not
│          re-required as a module: every later file uses `[]`, `[ x
│          ]`, `x :: xs`, and `[x; y; z]` for finite lists, and the
│          scope must already be active at parse time when those files
│          import the premise.
│
*)

Export ListNotations.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               PRIMITIVE SYNTAX                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The primitive object language of M001 is the closed
│          implicational/falsity fragment. There are no atomic
│          propositions, no propositional variables, and no
│          object-level substitution operation in this premise layer:
│          every formula is a finite tree built from `Bot` and `Imp`.
│
*)

Inductive Formula : Type :=
| Bot : Formula
| Imp : Formula -> Formula -> Formula.

(*
│
│          A context is a finite list of formulas. We do not quotient
│          by permutation, contraction, or extensional set equality:
│          later checker layers operate over this literal list
│          structure.
│
*)

(*      Gamma ::= [] | A :: Gamma and ctx_extend(A,Gamma) := A :: Gamma       *)

Definition Context := list Formula.

Definition ctx_empty : Context := nil.

Definition ctx_extend (A : Formula) (Gamma : Context) : Context :=
  cons A Gamma.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                AXIOM SOURCES                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Record AxiomSet : Type := {
  axiom_set_contains_bool : Formula -> bool
}.

Definition axiom_set_empty : AxiomSet :=
  {| axiom_set_contains_bool := fun _ => false |}.

(*
│
│          A `FiniteAxiomSet` is the certificate-facing counterpart of
│          `AxiomSet`: it stores a finite list of formulas. The
│          Boolean membership test and bridge into `AxiomSet` are
│          computational kernel material and are defined in
│          `M001_01__Kernel`.
│
*)

Record FiniteAxiomSet : Type := {
  finite_axiom_set_formulas : list Formula
}.

Definition finite_axiom_set_empty : FiniteAxiomSet :=
  {| finite_axiom_set_formulas := nil |}.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              REGULATOR PROFILE                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A regulator logic profile chooses which built-in logical
│          axiom schemas are available. The minimal profile exposes
│          only K/S; the EFQ profile adds the explicit `Imp Bot A`
│          schema.
│
*)

Inductive RegulatorLogicProfile : Type :=
| regulator_profile_minimal
| regulator_profile_with_efq.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                   REGULATOR THEORY AND BOOLEAN ENVIRONMENT                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `RegulatorTheory` is the object-level regulator
│          specification used by the checker: a logical profile
│          together with an external axiom source. This record is
│          still syntax, not model theory; it merely packages the two
│          finite-checker inputs that determine which `J_Axiom` lines
│          are available.
│
*)

Record RegulatorTheory : Type := {
  regulator_theory_profile : RegulatorLogicProfile;
  regulator_theory_axiom_set : AxiomSet
}.

Definition regulator_theory_with_axiom_set
    (profile : RegulatorLogicProfile)
    (T : AxiomSet) : RegulatorTheory :=
  {| regulator_theory_profile := profile;
     regulator_theory_axiom_set := T |}.

Definition regulator_theory_empty_minimal : RegulatorTheory :=
  regulator_theory_with_axiom_set
    regulator_profile_minimal
    axiom_set_empty.

Definition regulator_theory_empty_with_efq : RegulatorTheory :=
  regulator_theory_with_axiom_set
    regulator_profile_with_efq
    axiom_set_empty.

(*
│
│          A `BooleanEnvironment` is the minimal ambient wrapper for
│          regulator theories whose visible interface is Boolean. The
│          name is deliberately light storytelling rather than model
│          theory: inside this wrapper, regulator theories are
│          presented through Boolean checkers and Boolean axiom
│          availability. It is still not a context and not an axiom
│          set; contexts hold temporary assumptions, axiom sets answer
│          formula-availability queries, and Boolean environments only
│          collect the regulator theories that a later ambient layer
│          may expose.
│
*)

Record BooleanEnvironment : Type := {
  boolean_environment_regulator_theories : list RegulatorTheory
}.

Definition boolean_environment_empty : BooleanEnvironment :=
  {| boolean_environment_regulator_theories := nil |}.

Definition boolean_environment_extend_regulator_theory
    (R : RegulatorTheory)
    (E : BooleanEnvironment) : BooleanEnvironment :=
  {| boolean_environment_regulator_theories :=
       cons R E.(boolean_environment_regulator_theories) |}.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             PROOF SCRIPT GRAMMAR                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A proof line carries a claimed formula and a first-order
│          justification tag. The tag is syntactic data only:
│          `J_Assumption`, `J_Axiom`, and `J_MP i j` acquire their
│          checker meaning in `M001_01__Kernel`.
│
*)

Inductive Justification : Type :=
| J_Assumption
| J_Axiom
| J_MP : nat -> nat -> Justification.

Record ProofLine : Type := {
  line_formula : Formula;
  line_justification : Justification
}.

Definition Proof : Type := list ProofLine.
