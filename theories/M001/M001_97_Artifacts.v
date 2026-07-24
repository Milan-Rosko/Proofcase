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

  Certification and extraction boundary for the five canonical M001
  contracts. The assumption report certifies their aggregate; extraction
  starts only from the checker and the three retained proof transformations.

*)

From Stdlib Require Import Extraction.

From M001 Require Export M001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CERTIFIED CONTRACT                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Theorem m001_contract_qed :
  M001_CONTRACT.
Proof.
  unfold M001_CONTRACT.
  split.
  - exact formula_not_self_negation.
  - split.
    + exact regulator_theory_syntactic_adequacy_lemma.
    + split.
      * exact regulator_theory_deduction_checked.
      * split.
        -- exact regulator_theory_reductio_checked.
        -- unfold STRUCTURE.
           repeat split.
           ++ exact regulator_theory_mp_compose_checked_lemma.
           ++ exact regulator_theory_check_bool_context_monotone_lemma.
           ++ exact
                regulator_theory_check_bool_regulator_theory_monotone_lemma.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              ASSUMPTION REPORT                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Redirect "theories/M001/_appendix/_assumptions/m001_contract_qed"
  Print Assumptions m001_contract_qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               OCAML EXTRACTION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Extraction Language OCaml.

Extraction "theories/M001/_appendix/_artifacts/M001_checker"
  regulator_theory_check_bool
  finite_axiom_set_check_bool
  regulator_theory_mp_compose
  regulator_theory_deduction_transform
  regulator_theory_reductio_transform.
