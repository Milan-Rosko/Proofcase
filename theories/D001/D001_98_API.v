(*D001_98_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / D001_98_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Curated D001 public API shell. This file is the single import point for
  downstream projects (notably P002) that want the full Iterant arithmetic +
  operational + trace + universality surface without pinning individual
  implementation files. Artifact side effects live in `D001_99_Artifacts`.

*)

(*
│
│          The public API re-exports the full proof-facing Iterant
│          surface through the classical universality bridge.
│
*)

(*                       D001₀₀ ∧ ⋯ ∧ D001₀₉ → D001API                        *)

From D001 Require Export D001_00_Premises.
From D001 Require Export D001_01__Arithmetic_Base.
From D001 Require Export D001_02__Carryless_Bands.
From D001 Require Export D001_03__State_Codec.
From D001 Require Export D001_04__Machine_Definition.
From D001 Require Export D001_05__Transition_Relation.
From D001 Require Export D001_06__Trace_Witness.
From D001 Require Export D001_07__Step_Arithmetization.
From D001 Require Export D001_08__Universality.
From D001 Require Export D001_09__Classic_Universality.
