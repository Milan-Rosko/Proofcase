(*P001_98_QED.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / P001_98_QED                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file exposes the terminal certification theorem of P001.
  Assumption-report artifacts are recorded separately in `P001_99_Artifacts`.

  Certification closes by reusing the completed proof selected by the
  constructive switch.

*)

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                              SWITCH IMPORT                              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The certification layer imports the proof selected by the
│          switch.
│
*)

From P001.P001_92_Multiplexing Require Export P001_98_99__Switch.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                                  Q.E.D.                                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The final theorem certifies the contract by direct reuse of
│          the selected proof.
│
*)

Theorem pigeonhole_divisibility_qed : WITNESS.
Proof.
  exact UNCONDITIONAL_PROOF.
Qed.

(*
│
│          The terminal assumption report records the dependencies of
│          the certified endpoint.
│
*)

Redirect "theories/P001/_appendix/_assumptions/pigeonhole_divisibility_qed"
  Print Assumptions pigeonhole_divisibility_qed.
