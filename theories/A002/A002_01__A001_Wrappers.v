(*A002_01__A001_Wrappers.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / A002_01__A001_Wrappers                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  A001 wrapper layer for A002. We expose the certified carryless pairing
  surface through small arithmetic projections, a re-encoding test, and
  canonical destructuring predicates used before any A002 structured node is
  trusted.

  The A001 decoder is total on all natural numbers, so A002 never treats an
  arbitrary decoded pair as a valid structured object. A node is accepted as
  structured only when it is already fixed by the A001 encode/decode
  roundtrip.

*)

From A002 Require Export A002_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               A001 PROJECTIONS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `fst001` reads the first component exposed by the certified
│          A001 decoder. It is a projection, not a validity test.
│
*)

Definition fst001 (c : nat) : nat :=
  fst (decode c).

(*
│
│          `snd001` reads the second component exposed by the
│          certified A001 decoder. It is a projection, not a validity
│          test.
│
*)

Definition snd001 (c : nat) : nat :=
  snd (decode c).

(*
│
│          `recode001` decodes a number through A001 and then
│          re-encodes the visible pair. This is the canonical
│          representative associated with the input.
│
*)

Definition recode001 (c : nat) : nat :=
  encode (fst001 c) (snd001 c).

(*
│
│          `canonical001b` recognizes genuine A001 pair codes: a
│          number is canonical exactly when re-encoding its decoded
│          components returns the same number.
│
*)

Definition canonical001b (c : nat) : bool :=
  Nat.eqb (recode001 c) c.

(*
│
│          `is_pair001b c a b` is the local destructuring discipline
│          used throughout A002. It requires canonicity before
│          comparing the exposed components.
│
*)

Definition is_pair001b (c a b : nat) : bool :=
  canonical001b c
  && Nat.eqb (fst001 c) a
  && Nat.eqb (snd001 c) b.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                WRAPPER FACTS                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The first projection of a freshly encoded A001 pair is its
│          left input.
│
*)

Lemma fst001_encode :
  forall a b, fst001 (encode a b) = a.
Proof.
  intros a b.
  unfold fst001.
  rewrite decode_encode.
  reflexivity.
Qed.

(*
│
│          The second projection of a freshly encoded A001 pair is its
│          right input.
│
*)

Lemma snd001_encode :
  forall a b, snd001 (encode a b) = b.
Proof.
  intros a b.
  unfold snd001.
  rewrite decode_encode.
  reflexivity.
Qed.

(*
│
│          Every pair built with the certified A001 encoder is
│          canonical for the A002 destructuring discipline.
│
*)

Lemma canonical001b_encode :
  forall a b, canonical001b (encode a b) = true.
Proof.
  intros a b.
  unfold canonical001b, recode001.
  rewrite fst001_encode.
  rewrite snd001_encode.
  apply Nat.eqb_refl.
Qed.

(*
│
│          Freshly encoded pairs pass exact A001 pair destructuring.
│
*)

Lemma is_pair001b_encode :
  forall a b, is_pair001b (encode a b) a b = true.
Proof.
  intros a b.
  unfold is_pair001b.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*
│
│          A successful canonicality test can be transported to
│          propositional equality with the A001 recoding.
│
*)

Lemma canonical001b_eq :
  forall c,
    canonical001b c = true ->
    recode001 c = c.
Proof.
  intros c Hc.
  unfold canonical001b in Hc.
  apply Nat.eqb_eq.
  exact Hc.
Qed.

(*
│
│          Successful exact destructuring determines both exposed
│          components.
│
*)

Lemma is_pair001b_sound :
  forall c a b,
    is_pair001b c a b = true ->
    canonical001b c = true /\
    fst001 c = a /\
    snd001 c = b.
Proof.
  intros c a b Hpair.
  unfold is_pair001b in Hpair.
  repeat rewrite Bool.andb_true_iff in Hpair.
  destruct Hpair as [[Hcanon Hfst] Hsnd].
  repeat split.
  - exact Hcanon.
  - apply Nat.eqb_eq. exact Hfst.
  - apply Nat.eqb_eq. exact Hsnd.
Qed.
