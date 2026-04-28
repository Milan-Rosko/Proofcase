(*P001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / P001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This premise layer states the finite divisibility contract and deliberately
  exports the package-wide standard environment used by P001.

*)

From Stdlib Require Export Arith PeanoNat Bool Lia List.
Export ListNotations.
Global Open Scope list_scope.

(*
│
│          `PROPOSITIO` is the target statement: among any `n + 1`
│          distinct positive integers bounded by `2n`, two must be
│          related by divisibility. This standard
│          pigeonhole-divisibility result is referenced by Aigner's
│          “Proofs from THE BOOK”.
│
*)

(*                 ∀ n A. (∀ a ∈ A, 1 ≤ a ≤ 2n) → |A| = n + 1                 *)
(*              → ∃ a b, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ (a ∣ b ∨ b ∣ a)              *)

Definition PROPOSITIO : Prop :=
  forall n A,
    (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->
    NoDup A ->
    length A = n + 1 ->
    exists a b,
      In a A /\
      In b A /\
      a <> b /\
      (Nat.divide a b \/ Nat.divide b a).

(*
│
│          `WITNESS` names the proposition certified by the package.
│
*)

Definition WITNESS : Prop := PROPOSITIO.
