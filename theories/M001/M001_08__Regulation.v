(*M001_08__Regulation.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / M001_08__Regulation                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Minimal symbolic-regulator vocabulary shared with L002. A symbolic
  regulator contains only an output type, an instruction type, and a Boolean
  acceptance function. It adds no proof search, semantic interpretation,
  world structure, closure adapter, or evaluation principle.

*)

From M001 Require Export M001_07__Monotonicity.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              SYMBOLIC REGULATOR                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Record SymbolicRegulator : Type := {
  symbolic_regulator_output : Type;
  symbolic_regulator_instruction : Type;
  symbolic_regulator_accepts_bool :
    symbolic_regulator_instruction -> symbolic_regulator_output -> bool
}.

Definition S_λ : Type := SymbolicRegulator.

Definition symbolic_regulator_derivable
    (S : S_λ)
    (b : symbolic_regulator_output S) : Prop :=
  exists i : symbolic_regulator_instruction S,
    symbolic_regulator_accepts_bool S i b = true.
