(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Primitive syntax and finite checker data for M001.  The object
language contains only falsity and implication; contexts and proof scripts
are finite lists; a regulator theory contains a logical profile and a
Boolean axiom-membership function.  There is no semantic interpretation,
proof search, world structure, or evaluation machinery in this layer.]]@*)

(*@doc.pl@[[The trusted data boundary uses standard Booleans, lists, and
natural-number indices.  Later files define the total checker and the
executable proof transformations over exactly these values.]]@*)

(*@head.end@*)

(*@inline@[[`Bool.Bool` supplies the Boolean checker codomain and the `if` `andb` `orb` algebra used throughout.]]@*)

From Stdlib Require Export Bool.Bool.

(*@inline@[[`Lists.List` supplies the carrier for contexts, finite axiom sets, proof scripts, and regulator components.]]@*)

From Stdlib Require Export Lists.List.

(*@inline@[[`Arith_base` supplies the natural-number indexing used by `mp_valid_bool`, the deduction transformer's index map, and every `nth`-style accessor.]]@*)

From Stdlib Require Export Arith_base.

(*@inline@[[`ListNotations` is opened as a notation scope. Every later file uses `[]`, `[ x ]`, `x :: xs`, and `[x; y; z]` for finite lists, and the scope must already be active at parse time when those files import the premise.]]@*)

Export ListNotations.

(*@section@[[PRIMITIVE SYNTAX]]@*)

(*@inline@[[The primitive object language of M001 is the closed implicational/falsity fragment. There are no atomic propositions, no propositional variables, and no object-level substitution operation in this premise layer: every formula is a finite tree built from `Bot` and `Imp`.]]@*)

Inductive Formula : Type :=
| Bot : Formula
| Imp : Formula -> Formula -> Formula.

(*@inline@[[Object-language negation is implication to the primitive falsity
formula.  It belongs to the syntax boundary because no checker, theory, or
proof object is needed to state it.]]@*)

Definition formula_negation (A : Formula) : Formula :=
  Imp A Bot.

(*@inline@[[A context is a literal finite list of formulas. Later checker layers preserve its order and multiplicity.]]@*)

(*@unicodemath@[[Gamma ::= [] | A :: Gamma and ctx_extend(A,Gamma) := A :: Gamma]]@*)

Definition Context := list Formula.

Definition ctx_extend (A : Formula) (Gamma : Context) : Context :=
  cons A Gamma.

(*@section@[[AXIOM SOURCES]]@*)

Record AxiomSet : Type := {
  axiom_set_contains_bool : Formula -> bool
}.

(*@inline@[[A `FiniteAxiomSet` is the certificate-facing counterpart of `AxiomSet`: it stores a finite list of formulas. The Boolean membership test and bridge into `AxiomSet` are computational kernel material and are defined in `M001_01__Kernel`.]]@*)

Record FiniteAxiomSet : Type := {
  finite_axiom_set_formulas : list Formula
}.

(*@section@[[REGULATOR PROFILE]]@*)

(*@inline@[[A regulator logic profile chooses which built-in logical axiom schemas are available. The minimal profile exposes only K/S; the EFQ profile adds the explicit `Imp Bot A` schema.]]@*)

Inductive RegulatorLogicProfile : Type :=
| regulator_profile_minimal
| regulator_profile_with_efq.

(*@section@[[REGULATOR THEORY]]@*)

(*@inline@[[A `RegulatorTheory` is the object-level syntactic specification used by the checker: a logical profile together with an external axiom source. These two inputs determine which `J_Axiom` lines are available.]]@*)

Record RegulatorTheory : Type := {
  regulator_theory_profile : RegulatorLogicProfile;
  regulator_theory_axiom_set : AxiomSet
}.

Definition regulator_theory_with_axiom_set
    (profile : RegulatorLogicProfile)
    (T : AxiomSet) : RegulatorTheory :=
  {| regulator_theory_profile := profile;
     regulator_theory_axiom_set := T |}.

(*@section@[[PROOF SCRIPT GRAMMAR]]@*)

(*@inline@[[A proof line carries a claimed formula and a first-order justification tag. The tag is syntactic data only: `J_Assumption`, `J_Axiom`, and `J_MP i j` acquire their checker meaning in `M001_01__Kernel`.]]@*)

Inductive Justification : Type :=
| J_Assumption
| J_Axiom
| J_MP : nat -> nat -> Justification.

Record ProofLine : Type := {
  line_formula : Formula;
  line_justification : Justification
}.

Definition Proof : Type := list ProofLine.
