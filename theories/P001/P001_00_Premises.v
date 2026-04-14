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

  All downstream P001 files import this immutable file; the `Require Export`
  block makes the standard library available transitively throughout the
  package.

*)

From Stdlib Require Export Arith PeanoNat Bool Lia List.
Export ListNotations.
Global Open Scope list_scope.

(*
│
│          `PROPOSITIO` is our “quod esset” problem: “Show that among
│          any `n + 1` distinct positive integers bounded by `2n`, two
│          must be related by divisibility.” This anecdotal Erdős-Pósa
│          is referenced by Aigner's “Proofs from THE BOOK”.
│
*)

(*                 ∀ n A. (∀ a ∈ A, 1 ≤ a ≤ 2n) → |A|= n + 1                  *)
(*               → ∃ a b ∈ A such that a ≠ b ∧ (a | b ∨ b | a)                *)

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
│          There is of course “something” that witnesses the above.
│
*)


Definition WITNESS : Prop := PROPOSITIO.