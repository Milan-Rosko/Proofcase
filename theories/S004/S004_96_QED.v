(*S004_96_QED.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / S004_96_QED                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file exposes the terminal certification theorem of S004. The theorem
  certifies the public reduction contract fixed in `S004_00_Premises`: the
  center-tail-to-all-windows lift obligation implies nonperiodicity of the
  canonical Rule 30 center column.

  The endpoint certifies exactly the proposition named by `WITNESS`; the lift
  premise is part of that public contract.

*)

From S004 Require Export S004_01__Center_Normalization.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                    Q.E.D.                                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The certified reduction contract is the machine-checkable
│          dependency report: the lift obligation is the only premise
│          needed to close the challenge.
│
*)

Theorem certified_reduction_contract :
  RULE30_REDUCTION_CONTRACT.
Proof.
  exact challenge_from_lift.
Qed.

(*
│
│          The terminal theorem certifies the named S004 witness. Its
│          name records that this is a reduction contract, not the
│          bare challenge claim.
│
*)

Theorem rule30_periodicity_reduction_contract_qed : WITNESS.
Proof.
  exact certified_reduction_contract.
Qed.

(*
│
│          Specializing the certified contract to a lift witness
│          yields the challenge claim.
│
*)

Theorem certified_challenge_under_lift
  (Hlift : CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION) :
  RULE30_PERIODICITY_CHALLENGE.
Proof.
  exact (certified_reduction_contract Hlift).
Qed.

(*
│
│          The same specialization is exposed in the common `t > i`
│          formulation.
│
*)

Theorem certified_wolfram_form_under_lift
  (Hlift : CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION) :
  wolfram_no_eventual_center_period.
Proof.
  exact
    (center_nonperiodic_implies_wolfram_form
       (certified_challenge_under_lift Hlift)).
Qed.

(*
│
│          The terminal assumption reports record the dependencies of
│          the certified endpoints.
│
*)

Redirect "theories/S004/_appendix/_assumptions/certified_reduction_contract"
  Print Assumptions certified_reduction_contract.

Redirect "theories/S004/_appendix/_assumptions/rule30_periodicity_reduction_contract_qed"
  Print Assumptions rule30_periodicity_reduction_contract_qed.

Redirect "theories/S004/_appendix/_assumptions/certified_challenge_under_lift"
  Print Assumptions certified_challenge_under_lift.

Redirect "theories/S004/_appendix/_assumptions/certified_wolfram_form_under_lift"
  Print Assumptions certified_wolfram_form_under_lift.

Redirect "theories/S004/_appendix/_assumptions/certified_center_normalization_interface"
  Print Assumptions certified_center_normalization_interface.
