(*D001_01__Arithmetic_Base.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / D001_01__Arithmetic_Base                     │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Rather than rebuilding the Fibonacci and Zeckendorf apparatus locally, D001
  re-exports the required support and codec facts under machine-local names.

*)

From D001 Require Export D001_00_Premises.

(*
│
│          `Iterant_Z0` is the D001-facing alias of the canonical
│          Zeckendorf support extractor inherited from `A001`.
│
*)

Definition Iterant_Z0 : nat -> list nat := Z0.

(*
│
│          `Iterant_encode_pair` and `Iterant_decode_pair` re-export
│          the carryless pairing codec under machine-local names so
│          downstream developments can remain entirely inside the
│          `D001` namespace.
│
*)

Definition Iterant_encode_pair : nat -> nat -> nat := encode.

Definition Iterant_decode_pair : nat -> nat * nat := decode.

(*
│
│          `Iterant_Z0_sound` states that the imported support
│          extractor is numerically exact: summing the extracted
│          support reconstructs the original natural number.
│
*)

(*                      ∀ n, sum_fib(Iterant_Z0(n)) = n.                      *)

Theorem Iterant_Z0_sound :
  forall n, sum_fib (Iterant_Z0 n) = n.
Proof.
  exact Z0_sound.
Qed.

(*
│
│          `Iterant_Z0_valid` complements `Iterant_Z0_sound`: the
│          imported support is not only exact, but also
│          Zeckendorf-valid, which is the admissibility condition
│          required by the later machine constructions.
│
*)

(*                      ∀ n, zeck_valid(Iterant_Z0(n)).                       *)

Theorem Iterant_Z0_valid :
  forall n, zeck_valid (Iterant_Z0 n).
Proof.
  exact Z0_valid.
Qed.

(*
│
│          `Iterant_pair_roundtrip` transfers the carryless roundtrip
│          law into the machine namespace: encoding a pair and then
│          decoding the resulting code returns the original
│          coordinates.
│
*)

(*      ∀ a b, Iterant_decode_pair(Iterant_encode_pair(a, b)) = (a, b).       *)

Theorem Iterant_pair_roundtrip :
  forall a b,
    Iterant_decode_pair (Iterant_encode_pair a b) = (a, b).
Proof.
  exact decode_encode.
Qed.

(*
│
│          `Iterant_pair_injective` is the corresponding uniqueness
│          principle at the machine layer: equal codes force equality
│          of both encoded coordinates.
│
*)

(* Iterant_encode_pair(a, b) = Iterant_encode_pair(a', b') ⇒ a = a' ∧ b = b'. *)

Theorem Iterant_pair_injective :
  forall a b a' b',
    Iterant_encode_pair a b = Iterant_encode_pair a' b' ->
    a = a' /\ b = b'.
Proof.
  exact encode_injective.
Qed.
