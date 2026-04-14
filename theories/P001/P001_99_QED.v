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
      This file exposes the terminal certification artifact of P001.

      At Phase 0, certification closes by reusing the routed phase-zero witness
      exported through the switch.
*)

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                              ROUTER IMPORT                              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The certification layer depends on the routed surface
│          exported by the switch.
│
*)

From P001.P001_98_Currying Require Export P001_98_98_Multiplexer.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                                  Q.E.D.                                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The final theorem certifies the routed contract by direct
│          reuse of the witness.
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

Redirect "theories/P001/appendix/assumptions/pigeonhole_divisibility_qed" Print Assumptions pigeonhole_divisibility_qed.
