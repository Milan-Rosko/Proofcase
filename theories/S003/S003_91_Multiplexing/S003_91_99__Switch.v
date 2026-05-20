(*S003_91_99__Switch.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / S003_91_99__Switch                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file implements the constructive proof switch for S003. It exposes one
  selected proof realization under the stable name `UNCONDITIONAL_PROOF`.

  The switch makes the proof history explicit: the presentations are named
  separately, while the terminal theorem imports only the selected completed
  proof.

*)

From S003.S003_91_Multiplexing Require Export S003_91_02C__Proof.
