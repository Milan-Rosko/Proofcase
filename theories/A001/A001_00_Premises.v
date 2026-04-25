(*A001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / A001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  The minimal public contract for CARRYLESS PAIRING (A001). Encoder and
  decoder on `nat`, the roundtrip specification, the corresponding
  injectivity specification, and the contract proposition certified by the
  package. This file also re-exports the standard libraries used throughout
  A001.

*)

From Stdlib Require Export Arith PeanoNat Bool Lia List Ring ZArith Extraction.
Export ListNotations.
Global Open Scope list_scope.

Definition encode_t : Type := nat -> nat -> nat.

Definition decode_t : Type := nat -> nat * nat.

(*
│
│          `decode_encode_spec` is the core contract: decoding the
│          code produced from a pair recovers exactly that pair.
│
*)

Definition decode_encode_spec (encode : encode_t) (decode : decode_t) : Prop :=
  forall a b, decode (encode a b) = (a, b).

(*
│
│          Injectivity is exposed separately because it is one of the
│          citation theorems of the package, even though it is
│          derivable from the roundtrip law.
│
*)

Definition encode_injective_spec (encode : encode_t) : Prop :=
  forall a b a' b',
    encode a b = encode a' b' ->
    a = a' /\ b = b'.

(*
│
│          `pairing_contract` records the minimal correctness
│          condition: decoding after encoding recovers the original
│          pair.
│
*)

Definition pairing_contract (encode : encode_t) (decode : decode_t) : Prop :=
  decode_encode_spec encode decode.
