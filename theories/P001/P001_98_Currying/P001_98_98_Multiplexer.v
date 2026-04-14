(*P001_98_98_Multiplexer.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / P001_98_98_Multiplexer                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We implement a switch system as a project-level routing mechanism between a
  public contract, one or more internal proof realizations, and the terminal
  certification layer.

  The design intention is architectural rather than theorem-specific: the
  certification layer should depend on a stable routed interface, while
  internal proof phases may be curried or factorized without changing the
  external contracts (Premises and QED).

*)

(*
	From P001.P001_98_Currying Require Export P001_98_01A_Initial. 
	From P001.P001_98_Currying Require Export P001_98_01B_Expansion.
	From P001.P001_98_Currying Require Export P001_98_02B_Rewrite.
	From P001.P001_98_Currying Require Export P001_98_02C_Proof.
*)

From P001.P001_98_Currying Require Export P001_98_02C_Proof.
