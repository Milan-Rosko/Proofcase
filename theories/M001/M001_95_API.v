(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Public operational API surface for M001. Importing this file
exports primitive syntax, Boolean checking, deduction and reductio
transforms, checked and inductive derivability, MP composition, structural
monotonicity, and the symbolic-regulator acceptance and release vocabulary
used by L002.]]@*)

(*@doc.pl@[[Evaluation frames, regulator-instruction reification, symbolic
worlds, and closure adapters are deliberately outside this API.]]@*)

(*@head.end@*)

(*@section@[[PUBLIC EXPORT]]@*)

(*@inline@[[The public API cumulatively exports the retained M001 stack
through the symbolic-regulator release gate.]]@*)

(*@unicodemath@[[M001_API ≔ Syntax ⊕ Checker ⊕ Deduction ⊕ Reductio ⊕ Derivability ⊕ Composition ⊕ Adequacy ⊕ Monotonicity ⊕ SymbolicRegulator ⊕ Release]]@*)

From M001 Require Export M001_09__Regulated_Execution.

(*@section@[[CONTRACTS]]@*)

Definition SYNTAX : Prop :=
  forall A : Formula,
    A <> formula_negation A.

Definition ADEQUACY : Prop :=
  forall (R : RegulatorTheory) (Gamma : Context) (A : Formula),
    regulator_theory_checked_derivable R Gamma A <->
    regulator_theory_inductive_derivable R Gamma A.

Definition DEDUCTION : Prop :=
  forall (R : RegulatorTheory) (Gamma : Context)
         (A B : Formula) (p : Proof),
    regulator_theory_check_bool R (ctx_extend A Gamma) p B = true ->
    regulator_theory_check_bool R Gamma
      (regulator_theory_deduction_transform A p)
      (Imp A B) = true.

Definition REDUCTIO : Prop :=
  forall (R : RegulatorTheory) (Gamma : Context)
         (A : Formula) (p : Proof),
    regulator_theory_check_bool R (ctx_extend A Gamma) p Bot = true ->
    regulator_theory_check_bool R Gamma
      (regulator_theory_reductio_transform A p)
      (formula_negation A) = true.

Definition STRUCTURE : Prop :=
  (forall (R : RegulatorTheory) (Gamma : Context)
          (A B : Formula) (p_imp p_arg : Proof),
     regulator_theory_check_bool R Gamma p_imp (Imp A B) = true ->
     regulator_theory_check_bool R Gamma p_arg A = true ->
     regulator_theory_check_bool R Gamma
       (regulator_theory_mp_compose B p_imp p_arg) B = true) /\
  (forall (R : RegulatorTheory) (Gamma Delta : Context)
          (p : Proof) (A : Formula),
     context_included Gamma Delta ->
     regulator_theory_check_bool R Gamma p A = true ->
     regulator_theory_check_bool R Delta p A = true) /\
  (forall (R S : RegulatorTheory) (Gamma : Context)
          (p : Proof) (A : Formula),
     regulator_theory_included R S ->
     regulator_theory_check_bool R Gamma p A = true ->
     regulator_theory_check_bool S Gamma p A = true).

Definition M001_CONTRACT : Prop :=
  SYNTAX /\
  ADEQUACY /\
  DEDUCTION /\
  REDUCTIO /\
  STRUCTURE.
