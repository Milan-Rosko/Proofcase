(*L003_95_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / L003_95_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Public API and contract surface for L003. We re-export both post-nonclosure
  branches—the concrete compiled semantics and the indexed-judgment
  separation—and name the six propositions collected by the package contract.

  The contract definitions restate theorem shapes; their inhabitants are
  certified in `L003_97_Artifacts`. Downstream developments should normally
  import this file rather than the artifact layer.

*)

From L003 Require Export L003_03__Compiled_Countermachine.
From L003 Require Export L003_04__Indexed_Judgment.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        ABSTRACT NONCLOSURE CONTRACTS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The primary contract states evaluator-relative exclusion
│          under a supplied correct diagonal compiler.
│
*)

Definition EVALUATOR_RELATIVE_NONCLOSURE_CONTRACT : Prop :=
  forall (out : OutputRelation)
         (halt : HaltingRelation)
         (query : QueryCoding)
         (diagonal : DiagonalCompiler)
         (C : Code -> Prop)
         (h : Code),
    CompilerCorrect out halt query diagonal ->
    EvalC out halt query C h ->
    ~ C (diagonal h).

(*
│
│          The closed-domain contract excludes the existence of an
│          evaluator correct on a domain that contains every
│          evaluator-relative diagonal product.
│
*)

Definition DIAGONALLY_CLOSED_DOMAIN_EXCLUSION_CONTRACT : Prop :=
  forall (out : OutputRelation)
         (halt : HaltingRelation)
         (query : QueryCoding)
         (diagonal : DiagonalCompiler)
         (C : Code -> Prop),
    CompilerCorrect out halt query diagonal ->
    EvaluatorDiagonalClosure out halt query diagonal C ->
    ~ exists h : Code,
        EvalC out halt query C h.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            INDEXED-SELF CONTRACTS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Successful assigned-label checking does not, for every
│          configuration, entail binding to the active evaluator
│          label.
│
*)

Definition INDEXED_SELF_CHECKING_NONENTAILMENT_CONTRACT : Prop :=
  ~ (forall configuration : IndexedSelfConfiguration,
       SelfTokenChecks configuration ->
       SelfTokenBound configuration).

(*
│
│          Even when active-evaluator binding is supplied explicitly,
│          the bound evaluator must exclude its diagonal compiler
│          product from the correctness domain.
│
*)

Definition BOUND_EVALUATOR_NONCLOSURE_CONTRACT : Prop :=
  forall (out : OutputRelation)
         (halt : HaltingRelation)
         (query : QueryCoding)
         (diagonal : DiagonalCompiler)
         (C : Code -> Prop)
         (configuration : IndexedSelfConfiguration),
    CompilerCorrect out halt query diagonal ->
    BoundEvaluator out halt query C configuration ->
    ~ C (diagonal (active_evaluator configuration)).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         COMPILED-SEMANTICS CONTRACTS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The even/odd compiled semantics satisfies the abstract
│          diagonal compiler law for every base output relation and
│          query coding.
│
*)

Definition CONCRETE_COMPILER_CORRECTNESS_CONTRACT : Prop :=
  forall (base_out : OutputRelation)
         (query : QueryCoding),
    CompilerCorrect
      (CompiledOutput base_out query)
      (CompiledHalt base_out query)
      query
      compiled_diagonal_code.

(*
│
│          Every evaluator correct in the compiled semantics excludes
│          its odd diagonal product from the claimed correctness
│          domain.
│
*)

Definition CONCRETE_EVALUATOR_NONCLOSURE_CONTRACT : Prop :=
  forall (base_out : OutputRelation)
         (query : QueryCoding)
         (C : Code -> Prop)
         (h : Code),
    EvalC
      (CompiledOutput base_out query)
      (CompiledHalt base_out query)
      query C h ->
    ~ C (compiled_diagonal_code h).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          AGGREGATE PACKAGE CONTRACT                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `L003_CORE_CONTRACT` conjoins the two abstract nonclosure
│          results, the two indexed-self results, and the two concrete
│          compiled-semantics results.
│
*)

Definition L003_CORE_CONTRACT : Prop :=
  EVALUATOR_RELATIVE_NONCLOSURE_CONTRACT /\
  DIAGONALLY_CLOSED_DOMAIN_EXCLUSION_CONTRACT /\
  INDEXED_SELF_CHECKING_NONENTAILMENT_CONTRACT /\
  BOUND_EVALUATOR_NONCLOSURE_CONTRACT /\
  CONCRETE_COMPILER_CORRECTNESS_CONTRACT /\
  CONCRETE_EVALUATOR_NONCLOSURE_CONTRACT.
