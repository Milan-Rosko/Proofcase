(*M001_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / M001_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Computational artifacts for M001. This file emits assumption reports for
  the main constructive theorems and extracts the executable checker,
  proof-script transformers, certificate checkers, regulator-instruction
  checker, and symbolic-regulator acceptance functions. The artifacts are
  operational code, not an additional API layer and not a semantic validator.

  The extraction surface is intentionally narrow: Boolean predicates,
  proof-script accessors, proof checkers, deduction and reductio transforms,
  finite certificate checkers, instruction reification, and
  symbolic-regulator acceptance functions. No IO protocol, no semantic
  interpretation record, no classical target machinery, no proof field, no
  modal provability predicate, no arithmetic coding, and no self-recognition
  principle is extracted.

*)

From Stdlib Require Import Extraction.

From M001 Require Export M001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         ASSUMPTION REPORT ARTIFACTS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The assumption reports pin the main constructive chain: deduction,
  reductio, negative precomposition, and syntactic adequacy. They are
  generated as build artifacts and checked by the compile wrapper when this
  file is active.

(*           reports(M001) ≔ {deduction_checked, reductio_checked,            *)
(*                negative_precomposition, syntactic_adequacy}                *)
(*    ∀ report ∈ reports(M001). Print Assumptions(report) is emitted under    *)
(*                           _appendix/_assumptions                           *)

Redirect "theories/M001/_appendix/_assumptions/regulator_theory_deduction_checked"
  Print Assumptions regulator_theory_deduction_checked.

Redirect "theories/M001/_appendix/_assumptions/regulator_theory_reductio_checked"
  Print Assumptions regulator_theory_reductio_checked.

Redirect "theories/M001/_appendix/_assumptions/regulator_theory_not_checked_derivable_precompose_lemma"
  Print Assumptions regulator_theory_not_checked_derivable_precompose_lemma.

Redirect "theories/M001/_appendix/_assumptions/regulator_theory_syntactic_adequacy_lemma"
  Print Assumptions regulator_theory_syntactic_adequacy_lemma.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               OCAML EXTRACTION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The extracted artifact is the executable checker package. Its roots are the
  formula/context decidable structure, axiom recognizers, proof-script
  checker, deduction and reductio transforms, finite reductio certificate
  checkers, instruction reification, and symbolic-regulator acceptance
  functions.

(*       extract(M001) : checker ∪ transforms ∪ certificate_checkers ∪        *)
(*                 instruction_checker ∪ symbolic_acceptance                  *)
(* target(M001) = theories/M001/_appendix/_artifacts/regulator_theory_checker *)

Extraction Language OCaml.

Extraction "theories/M001/_appendix/_artifacts/regulator_theory_checker"
  formula_eq_bool
  ctx_mem_bool
  finite_axiom_set_contains_bool
  finite_axiom_set_to_axiom_set
  k_axiom_bool
  s_axiom_bool
  efq_axiom_bool
  logical_axiom_bool
  available_axiom_bool
  nth_formula
  pl_assumption
  pl_axiom
  pl_mp
  last_formula
  mp_valid_bool
  proof_line_valid_bool
  proof_line_check_bool
  proof_script_check_from_bool
  regulator_theory_check_bool
  finite_axiom_set_to_regulator_theory
  finite_axiom_set_check_bool
  regulator_theory_check_minimal_bool
  regulator_theory_deduction_transform
  formula_negation
  regulator_theory_reductio_transform
  computed_reductio_certificate_check_bool
  paired_reductio_certificate_check_bool
  raw_reductio_certificate_check_bool
  make_computed_reductio_certificate
  make_raw_reductio_certificate
  regulator_instruction_output
  regulator_instruction_to_line
  proof_line_to_regulator_instruction
  regulator_instruction_valid_bool
  regulator_theory_regulates_bool
  finite_axiom_set_regulates_bool.
