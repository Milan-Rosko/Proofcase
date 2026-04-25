(*P001_99_QED.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / P001_99_QED                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

(*
      This file exposes the terminal certification theorem of P001.

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

From P001.P001_98_Multiplexing Require Export P001_98_98__Switch.

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

Definition WITNESS : Prop := PROPOSITIO.

Theorem pigeonhole_divisibility_qed : WITNESS.
Proof.
  exact UNCONDITIONAL_PROOF.
Qed.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                            PRINT ASSUMPTIONS                            │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

Redirect "theories/P001/appendix/_assumptions/pigeonhole_divisibility_qed" Print Assumptions pigeonhole_divisibility_qed.
