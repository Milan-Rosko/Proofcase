(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This file imports the full A001 “Carryless Pairing” development as the arithmetic substrate of the Vector Iterant machine layer.]]@*)

(*@doc.pl@[[Rather than rebuilding the Fibonacci and Zeckendorf apparatus locally, D001 re-exports the required support and codec facts under machine-local names.]]@*)

(*@head.end@*)

From A001 Require Export A001_03__Pair_Unpair_Correct.

(*@inline@[[`FM_Z0` is the D001-facing alias of the canonical Zeckendorf support extractor inherited from `A001`.]]@*)

Definition FM_Z0 : nat -> list nat := Z0.

(*@inline@[[`FM_encode_pair` and `FM_decode_pair` re-export the carryless pairing codec under machine-local names so downstream developments can remain entirely inside the `D001` namespace.]]@*)

Definition FM_encode_pair : nat -> nat -> nat := encode.

Definition FM_decode_pair : nat -> nat * nat := decode.

(*@inline@[[`FM_Z0_sound` states that the imported support extractor is numerically exact: summing the extracted support reconstructs the original natural number.]]@*)

(*@unicodemath@[[∀ n, sum_fib(FM_Z0(n)) = n.]]@*)

Theorem FM_Z0_sound :
  forall n, sum_fib (FM_Z0 n) = n.
Proof.
  exact Z0_sound.
Qed.

(*@inline@[[`FM_Z0_valid` complements `FM_Z0_sound`: the imported support is not only exact, but also Zeckendorf-valid, which is the admissibility condition required by the later machine constructions.]]@*)

(*@unicodemath@[[∀ n, zeck_valid(FM_Z0(n)).]]@*)

Theorem FM_Z0_valid :
  forall n, zeck_valid (FM_Z0 n).
Proof.
  exact Z0_valid.
Qed.

(*@inline@[[`FM_pair_roundtrip` transfers the carryless roundtrip law into the machine namespace: encoding a pair and then decoding the resulting code returns the original coordinates.]]@*)

(*@unicodemath@[[∀ a b, FM_decode_pair(FM_encode_pair(a, b)) = (a, b).]]@*)

Theorem FM_pair_roundtrip :
  forall a b,
    FM_decode_pair (FM_encode_pair a b) = (a, b).
Proof.
  exact decode_encode.
Qed.

(*@inline@[[`FM_pair_injective` is the corresponding uniqueness principle at the machine layer: equal codes force equality of both encoded coordinates.]]@*)

(*@unicodemath@[[FM_encode_pair(a, b) = FM_encode_pair(a', b') ⇒ a = a' ∧ b = b'.]]@*)

Theorem FM_pair_injective :
  forall a b a' b',
    FM_encode_pair a b = FM_encode_pair a' b' ->
    a = a' /\ b = b'.
Proof.
  exact encode_injective.
Qed.
