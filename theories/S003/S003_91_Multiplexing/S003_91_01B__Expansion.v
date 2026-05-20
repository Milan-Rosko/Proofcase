(*S003_91_01B__Expansion.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / S003_91_01B__Expansion                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This conjectural multiplexing presentation imports the reframed expansion
  from `S003_01` and records that proving that expansion would already yield
  the witness. It is part of the proof history, not the completed proof
  selected by the terminal switch.

*)

From S003 Require Export S003_01__Reframing.

(*
│
│          The historical expansion presentation keeps only the open
│          expanded obligation, reusing the canonical
│          `first_expansion` shape from the reframing layer.
│
*)

Conjecture first_expansion_holds : first_expansion.

(*
│
│          The expanded obligation supplies a proof of `WITNESS`
│          through the reframing theorem.
│
*)

Theorem UNCONDITIONAL_PROOF : WITNESS.
Proof.
  apply first_expansion_implies_WITNESS.
  exact first_expansion_holds.
Qed.
