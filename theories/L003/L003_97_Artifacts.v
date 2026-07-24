(*L003_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / L003_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Certification and assumption-report layer for L003. We inhabit each public
  contract from its corresponding theorem, assemble the aggregate package
  endpoint, and redirect assumption reports for the six citation results.

*)

From L003 Require Export L003_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         CERTIFIED CONTRACT ENDPOINTS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The abstract evaluator-relative nonclosure theorem inhabits
│          its public contract.
│
*)

Theorem certified_evaluator_relative_nonclosure_contract :
  EVALUATOR_RELATIVE_NONCLOSURE_CONTRACT.
Proof.
  exact evaluator_relative_nonclosure.
Qed.

(*
│
│          The diagonally closed-domain exclusion theorem inhabits its
│          public contract.
│
*)

Theorem certified_diagonally_closed_domain_exclusion_contract :
  DIAGONALLY_CLOSED_DOMAIN_EXCLUSION_CONTRACT.
Proof.
  exact no_total_evaluator_on_diagonally_closed_domain.
Qed.

(*
│
│          The indexed-label countermodel inhabits the
│          checking-nonentailment contract.
│
*)

Theorem certified_indexed_self_checking_nonentailment_contract :
  INDEXED_SELF_CHECKING_NONENTAILMENT_CONTRACT.
Proof.
  exact indexed_self_checking_does_not_supply_binding.
Qed.

(*
│
│          The bound-evaluator theorem inhabits the corresponding
│          nonclosure contract.
│
*)

Theorem certified_bound_evaluator_nonclosure_contract :
  BOUND_EVALUATOR_NONCLOSURE_CONTRACT.
Proof.
  exact bound_evaluator_relative_nonclosure.
Qed.

(*
│
│          The even/odd compiled semantics inhabits the concrete
│          compiler-correctness contract.
│
*)

Theorem certified_concrete_compiler_correctness_contract :
  CONCRETE_COMPILER_CORRECTNESS_CONTRACT.
Proof.
  exact compiled_countermachine_correct.
Qed.

(*
│
│          The specialized nonclosure theorem inhabits the concrete
│          evaluator contract.
│
*)

Theorem certified_concrete_evaluator_nonclosure_contract :
  CONCRETE_EVALUATOR_NONCLOSURE_CONTRACT.
Proof.
  exact concrete_evaluator_relative_nonclosure.
Qed.

(*
│
│          `l003_core_qed` is the aggregate certified endpoint for all
│          six L003 contracts.
│
*)

Theorem l003_core_qed :
  L003_CORE_CONTRACT.
Proof.
  unfold L003_CORE_CONTRACT.
  split.
  - exact certified_evaluator_relative_nonclosure_contract.
  - split.
    + exact certified_diagonally_closed_domain_exclusion_contract.
    + split.
      * exact certified_indexed_self_checking_nonentailment_contract.
      * split.
        -- exact certified_bound_evaluator_nonclosure_contract.
        -- split.
           ++ exact certified_concrete_compiler_correctness_contract.
           ++ exact certified_concrete_evaluator_nonclosure_contract.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              ASSUMPTION REPORTS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The following redirects materialize the global-context
│          assumptions of the primary abstract, indexed-self,
│          concrete, and aggregate endpoints under
│          `_appendix/_assumptions/`.
│
*)

Redirect "theories/L003/_appendix/_assumptions/evaluator_relative_nonclosure"
  Print Assumptions evaluator_relative_nonclosure.

Redirect "theories/L003/_appendix/_assumptions/no_total_evaluator_on_diagonally_closed_domain"
  Print Assumptions no_total_evaluator_on_diagonally_closed_domain.

Redirect "theories/L003/_appendix/_assumptions/indexed_self_checking_does_not_supply_binding"
  Print Assumptions indexed_self_checking_does_not_supply_binding.

Redirect "theories/L003/_appendix/_assumptions/compiled_countermachine_correct"
  Print Assumptions compiled_countermachine_correct.

Redirect "theories/L003/_appendix/_assumptions/concrete_evaluator_relative_nonclosure"
  Print Assumptions concrete_evaluator_relative_nonclosure.

Redirect "theories/L003/_appendix/_assumptions/l003_core_qed"
  Print Assumptions l003_core_qed.
