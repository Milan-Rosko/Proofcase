(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Premise layer for A001/CARRYLESS PAIRING. We fix the shared standard-library environment and name the abstract encoder, decoder, roundtrip law, injectivity law, and package contract that the later files certify.]]@*)

(*@head.end@*)

From Stdlib Require Export Arith PeanoNat Bool Lia List Ring ZArith Extraction.
Export ListNotations.
Global Open Scope list_scope.

(*@inline@[[The encoder type maps two natural numbers to one natural-number code.]]@*)

Definition encode_t : Type := nat -> nat -> nat.

(*@inline@[[The decoder type maps one natural-number code back to a pair of natural numbers.]]@*)

Definition decode_t : Type := nat -> nat * nat.

(*@inline@[[`decode_encode_spec` is the roundtrip contract for a candidate encoder and decoder.]]@*)

Definition decode_encode_spec (encode : encode_t) (decode : decode_t) : Prop :=
  forall a b, decode (encode a b) = (a, b).

(*@inline@[[`encode_injective_spec` records the corresponding one-code-one-pair property.]]@*)

Definition encode_injective_spec (encode : encode_t) : Prop :=
  forall a b a' b',
    encode a b = encode a' b' ->
    a = a' /\ b = b'.

(*@inline@[[`pairing_contract` packages the roundtrip law as the minimal certified surface.]]@*)

Definition pairing_contract (encode : encode_t) (decode : decode_t) : Prop :=
  decode_encode_spec encode decode.
