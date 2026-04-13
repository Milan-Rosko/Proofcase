(*P001_98_01A_Initial.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / P001_98_01A_Initial                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  At the present “template” stage, we assume that we can prove our original
  statement (`PROPOSITION`).

*)

From P001 Require Export P001_00_Premises.

(*
│
│          We assume by conjecture: We can prove by
│          `UNCONDITIONAL_PROOF` that “Among any collection of n+1
│          pairwise distinct integers chosen from the integers 1
│          through 2n, there must exist at least two distinct members
│          of that collection such that one of them divides the other“
│          follows from `WITNESS`.
│
*)

Conjecture UNCONDITIONAL_PROOF : WITNESS.
