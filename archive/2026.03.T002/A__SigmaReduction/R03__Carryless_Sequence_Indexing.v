(*

  Proofcase / T002 / Carryless Sequence Indexing
  ==============================================

    Overview
    --------

      We develop the Carryless Sequence Indexing layer used by the T002
      sigma-reduction route. This file packages the definitions and lemmas
      exported to later modules in the same route.
*)

From T002 Require Export R01__Foundation_Fibonacci.
From T002 Require Export R02__Foundation_Zeckendorf.

Definition hd0 (u : nat) : nat := fst (unpair P0 u).
Definition tl0 (u : nat) : nat := snd (unpair P0 u).

(* Bounded unpair recursion for list-like codes. *)
Fixpoint tailn (i s : nat) : nat :=
  match i with
  | 0 => s
  | S k => tl0 (tailn k s)
  end.

Definition line0 (s i : nat) : nat := hd0 (tailn i s).
