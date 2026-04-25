(*P001_98_98__Switch.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / P001_98_98__Switch                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file implements the constructive proof switch for P001. It exposes one
  selected proof realization under the stable name `UNCONDITIONAL_PROOF`.

  The switch makes the proof history explicit: earlier realizations remain
  available as named files, while the terminal theorem imports only the
  selected completed proof.

*)

From P001.P001_98_Multiplexing Require Export P001_98_02C__Proof.
