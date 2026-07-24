(*L001_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / L001_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Certification boundary for the six canonical L001 contracts. Derived
  corollaries remain in the public API but do not enlarge the certified
  contract surface.

*)

From L001 Require Export L001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CERTIFIED CONTRACT                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Theorem l001_contract_qed :
  L001_CONTRACT.
Proof.
  repeat split.
  - exact local_branch_collapse.
  - exact core_diagonal_obstruction.
  - exact eval_bottom_negfixp.
  - exact local_signed_obstruction.
  - exact local_membership_obstruction.
  - exact closure_refutation_inhabited.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              ASSUMPTION REPORT                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Redirect "theories/L001/_appendix/_assumptions/l001_contract_qed"
  Print Assumptions l001_contract_qed.
