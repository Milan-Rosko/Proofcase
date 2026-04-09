(*A001_02__Pair_Unpair_Correct.v*)

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                Copyright and author remark. Author(s):  │
│             ╭╮╮╮─╮             Milan Rosko  https://www.milanrosko.com  │
│             ││││╭╯             Licence. This file is distributed under  │
│              ╯╯╯╰              the Mozilla Public License Version 2.0,  │
│                                visit https://www.mozilla.org/en-US/MPL  │
└─────────────────────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────────────────────┐
│          Proofcase / A001_02__Pair_Unpair_Correct : “Pairing”           │
└─────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file unifies the forward and inverse directions of the concrete
  carryless pairing device. It defines the specialized encoder and
  decoder over the distinguished Fibonacci base and proves the core 
  correctness facts: roundtrip and injectivity.
  
*)

From A001 Require Export A001_01__Base_Fibonacci.

Definition boundary (x : nat) : nat :=
  B base_params x.

(*                     boundary(x) = B(x) = 2·r0(x)                     *)

Definition even_band_of (x : nat) : list nat :=
  even_band base_params x.

Definition odd_band_of (x y : nat) : list nat :=
  odd_band base_params x y.

Definition encode (a b : nat) : nat :=
  sum_fib (odd_band_of a b ++ even_band_of a).

(*
│
│             `encode` is the concrete carryless pairing map.
│             It places the support of `b` in the odd band
│             above the boundary determined by `a`, places
│             the support of `a` in the even band below that
│             boundary, and then reads the combined support
│             through `sum_fib`.
│
*)

Theorem encode_as_sum :
  forall a b,
    encode a b = sum_fib (odd_band_of a b ++ even_band_of a).
Proof.
  reflexivity.
Qed.

Lemma encode_eq_pair :
  forall a b,
    encode a b = pair base_params a b.
Proof.
  intros a b.
  symmetry.
  exact (pair_base_as_odd_even_sum a b).
Qed.

Theorem support_of_encode :
  forall a b,
    Z0 (encode a b) = odd_band_of a b ++ even_band_of a.
Proof.
  intros a b.
  rewrite encode_eq_pair.
  exact (Z0_pair_is_concat a b).
Qed.

Corollary even_support_of_encode :
  forall a b,
    filter is_even (Z0 (encode a b)) = even_band_of a.
Proof.
  intros a b.
  rewrite encode_eq_pair.
  exact (Z0_even_split a b).
Qed.

Corollary odd_support_of_encode :
  forall a b,
    filter (odd_ge_B1 (boundary a)) (Z0 (encode a b)) = odd_band_of a b.
Proof.
  intros a b.
  rewrite encode_eq_pair.
  exact (Z0_odd_split a b).
Qed.

Definition half_even_support : list nat -> list nat :=
  half_even_indices.

Definition odd_above_boundary (x k : nat) : bool :=
  odd_ge_B1 (boundary x) k.

Definition odd_support_indices (x : nat) (zn : list nat) : list nat :=
  y_indices (boundary x) zn.

Definition decode (c : nat) : nat * nat :=
  let zn := Z0 c in
  let x := sum_fib (half_even_support zn) in
  let y := sum_fib (odd_support_indices x zn) in
  (x, y).

(*
│
│             `decode` reverses the support splitting scheme
│             of `encode`. It first reconstructs the left
│             component from the even part of the canonical
│             support of `c`, then reconstructs the right
│             component from the odd part lying above the
│             recovered boundary.
│
*)

Lemma div2_two :
  forall n, div2 (two n) = n.
Proof.
  induction n as [|n IH].
  - simpl. reflexivity.
  - rewrite two_S. simpl. rewrite IH. reflexivity.
Qed.

Lemma add_sub_cancel_l :
  forall a b, a + b - a = b.
Proof.
  induction a as [|a IH]; intro b; simpl.
  - rewrite Nat.sub_0_r. reflexivity.
  - apply IH.
Qed.

Lemma map_div2_even_band :
  forall x, map div2 (even_band_of x) = Z0 x.
Proof.
  intro x.
  unfold even_band_of, even_band.
  rewrite map_map.
  rewrite <- map_id.
  apply map_ext.
  intro a.
  apply div2_two.
Qed.

Lemma decode_encode_odd :
  forall x j,
    decode_odd_index (boundary x) (boundary x + two_j_minus1 j) = j.
Proof.
  intros x j.
  unfold decode_odd_index, boundary, two_j_minus1.
  rewrite (add_sub_cancel_l (B base_params x) (Nat.pred (two j))).
  destruct j as [|j'].
  - simpl. reflexivity.
  - rewrite two_S. simpl. rewrite div2_two. reflexivity.
Qed.

Lemma map_decode_odd_band :
  forall x y,
    map (decode_odd_index (boundary x)) (odd_band_of x y) = Z0 y.
Proof.
  intros x y.
  unfold odd_band_of, odd_band.
  rewrite map_map.
  rewrite <- map_id.
  apply map_ext.
  intro a.
  apply decode_encode_odd.
Qed.

Lemma sum_fib_half_even_encode :
  forall x y,
    sum_fib (half_even_support (Z0 (encode x y))) = x.
Proof.
  intros x y.
  unfold half_even_support, half_even_indices.
  rewrite even_support_of_encode.
  rewrite map_div2_even_band.
  apply Z0_sound.
Qed.

Lemma sum_fib_odd_support_encode :
  forall x y,
    sum_fib (odd_support_indices x (Z0 (encode x y))) = y.
Proof.
  intros x y.
  unfold odd_support_indices, y_indices.
  rewrite odd_support_of_encode.
  rewrite map_decode_odd_band.
  apply Z0_sound.
Qed.

Theorem decode_encode :
  forall a b, decode (encode a b) = (a, b).
Proof.
  intros a b.
  unfold decode.
  set (zn := Z0 (encode a b)).
  assert (Hx : sum_fib (half_even_support zn) = a).
  {
    subst zn.
    apply sum_fib_half_even_encode.
  }
  rewrite Hx.
  assert (Hy : sum_fib (odd_support_indices a zn) = b).
  {
    subst zn.
    apply sum_fib_odd_support_encode.
  }
  rewrite Hy.
  reflexivity.
Qed.

Theorem encode_injective :
  forall a b a' b',
    encode a b = encode a' b' ->
    a = a' /\ b = b'.
Proof.
  intros a b a' b' Hcode.
  apply (f_equal decode) in Hcode.
  rewrite !decode_encode in Hcode.
  injection Hcode as Ha Hb.
  split; assumption.
Qed.

Corollary decode_encode_fst :
  forall a b, fst (decode (encode a b)) = a.
Proof.
  intros a b.
  rewrite decode_encode.
  reflexivity.
Qed.

Corollary decode_encode_snd :
  forall a b, snd (decode (encode a b)) = b.
Proof.
  intros a b.
  rewrite decode_encode.
  reflexivity.
Qed.

Example decode_encode_1_1 :
  decode (encode 1 1) = (1, 1).
Proof. reflexivity. Qed.

Example decode_encode_3_5 :
  decode (encode 3 5) = (3, 5).
Proof. reflexivity. Qed.

Redirect "theories/A001/appendix/assumptions/decode_encode"
  Print Assumptions decode_encode.

Redirect "theories/A001/appendix/assumptions/encode_injective"
  Print Assumptions encode_injective.

Extraction Language OCaml.
Extraction "carryless_pairing" encode decode.
