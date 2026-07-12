(*M001_95_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / M001_95_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Public operational API surface for M001. Importing this file exports the
  active regulator-theory stack: primitive syntax, Boolean checking,
  deduction and reductio transforms, checked and inductive derivability, MP
  composition, negative precomposition, symbolic regulators, the
  closure/equivalence interface, and evaluation-closure bridges.

  The syntactic operational API exposes `regulator_theory_check_bool`,
  `regulator_theory_checked_derivable`, `regulator_theory_closure`,
  `SymbolicRegulator`, and `RegulatorEvaluationFrame`.

*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                PUBLIC EXPORT                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The public API cumulatively exports the completed M001
│          stack through `M001_09__Evaluation_Closure`. Importers can
│          use this file as the stable operational regulator-theory
│          surface.
│
*)

(*    M001_API ≔ Premises ⊕ Kernel ⊕ Deduction ⊕ Falsity ⊕ Certificates ⊕     *)
(*Application ⊕ Adequacy ⊕ NegativeTransport ⊕ Regulation ⊕ EvaluationClosure *)

From M001 Require Export M001_09__Evaluation_Closure.
