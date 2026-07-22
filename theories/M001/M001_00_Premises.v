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

  Primitive syntax and finite checker data for M001. The object language
  contains only falsity and implication; contexts and proof scripts are
  finite lists; a regulator theory contains a logical profile and a Boolean
  axiom-membership function. There is no semantic interpretation, proof
  search, world structure, or evaluation machinery in this layer.

  The trusted data boundary uses standard Booleans, lists, and natural-number
  indices. Later files define the total checker and the executable proof
  transformations over exactly these values.

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
│          `ListNotations` is opened as a notation scope. Every later
│          file uses `[]`, `[ x ]`, `x :: xs`, and `[x; y; z]` for
│          finite lists, and the scope must already be active at parse
│          time when those files import the premise.
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
│          Object-language negation is implication to the primitive
│          falsity formula. It belongs to the syntax boundary because
│          no checker, theory, or proof object is needed to state it.
│
*)

Definition formula_negation (A : Formula) : Formula :=
  Imp A Bot.

(*
│
│          A context is a literal finite list of formulas. Later
│          checker layers preserve its order and multiplicity.
│
*)

(*      Gamma ::= [] | A :: Gamma and ctx_extend(A,Gamma) := A :: Gamma       *)

Definition Context := list Formula.

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
│                               REGULATOR THEORY                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `RegulatorTheory` is the object-level syntactic
│          specification used by the checker: a logical profile
│          together with an external axiom source. These two inputs
│          determine which `J_Axiom` lines are available.
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
