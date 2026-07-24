(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Certification boundary for the six canonical L001 contracts.
Derived corollaries remain in the public API but do not enlarge the certified
contract surface.]]@*)

(*@head.end@*)

From L001 Require Export L001_95_API.

(*@section@[[CERTIFIED CONTRACT]]@*)

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

(*@section@[[ASSUMPTION REPORT]]@*)

Redirect "theories/L001/_appendix/_assumptions/l001_contract_qed"
  Print Assumptions l001_contract_qed.
