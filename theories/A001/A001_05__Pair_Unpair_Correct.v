(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Concrete certified surface for A001 carryless pairing. We specialize the parametric Fibonacci-base construction to the distinguished support engine, define `encode` and `decode`, and establish roundtrip and injectivity.]]@*)

(*@doc.pl@[[The preceding files develop the Zeckendorf support machinery and the carryless band decomposition. The present file is the first user-facing arithmetic surface, packaging those structural results as a concrete pairing function and its inverse.]]@*)

(*@doc.pl@[[The exported theorem names in this layer are intentionally short: downstream developments depend on `encode`, `decode`, `decode_encode`, and `encode_injective` as the certified pairing interface.]]@*)

(*@head.end@*)

From A001 Require Export A001_00_Premises.
From A001 Require Export A001_04__Carryless_Bands.

(*@unicodemath@[[boundary(x) ≔ B(x) = 2 · r0(x).]]@*)

Definition boundary (x : nat) : nat :=
  B base_params x.

Definition even_band_of (x : nat) : list nat :=
  even_band base_params x.

Definition odd_band_of (x y : nat) : list nat :=
  odd_band base_params x y.

(*@inline@[[`encode` is the concrete carryless map. We place the support of `b` in the odd band above the boundary determined by `a`, place the support of `a` in the even band below that boundary, and evaluate the combined support through `sum_fib`.]]@*)

(*@unicodemath@[[encode(a, b) = Σ_F(even_band(a) ⧺ odd_band(a, b)).]]@*)

Definition encode (a b : nat) : nat :=
  sum_fib (odd_band_of a b ++ even_band_of a).

Theorem encode_as_sum :
  forall a b,
    encode a b = sum_fib (odd_band_of a b ++ even_band_of a).
Proof.
  reflexivity.
Qed.

(*@inline@[[`encode` is the abstract `pair` specialized to `base_params`.]]@*)

Lemma encode_eq_pair :
  forall a b,
    encode a b = pair base_params a b.
Proof.
  intros a b.
  symmetry.
  exact (pair_base_as_odd_even_sum a b).
Qed.

(*@inline@[[The canonical Zeckendorf support of an encoded pair splits into the odd band for the right component and the even band for the left component.]]@*)

(*@unicodemath@[[Z0(encode(a, b)) = odd_band(a, b) ⧺ even_band(a).]]@*)

Theorem support_of_encode :
  forall a b,
    Z0 (encode a b) = odd_band_of a b ++ even_band_of a.
Proof.
  intros a b.
  rewrite encode_eq_pair.
  exact (Z0_pair_is_concat a b).
Qed.

(*@inline@[[The left support is recovered by filtering the canonical support of the code for even indices.]]@*)

Corollary even_support_of_encode :
  forall a b,
    filter Nat.even (Z0 (encode a b)) = even_band_of a.
Proof.
  intros a b.
  rewrite encode_eq_pair.
  exact (Z0_even_split a b).
Qed.

(*@inline@[[The right support is recovered by selecting precisely those odd indices that lie beyond the boundary determined by the left coordinate.]]@*)

Corollary odd_support_of_encode :
  forall a b,
    filter (odd_ge_B1 (boundary a)) (Z0 (encode a b)) = odd_band_of a b.
Proof.
  intros a b.
  rewrite encode_eq_pair.
  exact (Z0_odd_split a b).
Qed.

(*@unicodemath@[[half_even_support(zn) ≔ { k / 2 ∣ k ∈ zn ∧ 2 ∣ k }.]]@*)

Definition half_even_support : list nat -> list nat :=
  half_even_indices.

(*@unicodemath@[[odd_above_boundary(x, k) = true ⇔ 2 ∤ k ∧ boundary(x) + 1 ≤ k.]]@*)

Definition odd_above_boundary (x k : nat) : bool :=
  odd_ge_B1 (boundary x) k.

(*@unicodemath@[[odd_support_indices(x, zn) ≔ { (k − boundary(x) + 1) / 2]][[∣ k ∈ zn ∧ 2 ∤ k ∧ boundary(x) + 1 ≤ k }.]]@*)

Definition odd_support_indices (x : nat) (zn : list nat) : list nat :=
  y_indices (boundary x) zn.

(*@inline@[[`decode` inverts the support-splitting scheme of `encode`. We first reconstruct the left component from the even support of `c`, and then use the recovered boundary to reconstruct the right component from the odd support above it.]]@*)

Definition decode (c : nat) : nat * nat :=
  let zn := Z0 c in
  let x := sum_fib (half_even_support zn) in
  let y := sum_fib (odd_support_indices x zn) in
  (x, y).

Lemma div2_two : forall n, Nat.div2 (two n) = n.
Proof.
  intro n. unfold two. replace (n + n) with (2 * n) by lia.
  apply Nat.div2_double.
Qed.

Lemma add_sub_cancel_l : forall a b, a + b - a = b.
Proof. intros. lia. Qed.

(*@inline@[[Halving the even band inverts the doubling map, recovering the original Zeckendorf support of the left coordinate.]]@*)

Lemma map_div2_even_band :
  forall x, map Nat.div2 (even_band_of x) = Z0 x.
Proof.
  intro x.
  unfold even_band_of, even_band.
  rewrite map_map.
  rewrite <- map_id.
  apply map_ext.
  intro a.
  apply div2_two.
Qed.

(*@unicodemath@[[decode_odd_index(boundary(x), boundary(x) + (2j − 1)) = j.]]@*)

Lemma decode_encode_odd :
  forall x j,
    decode_odd_index (boundary x) (boundary x + two_j_minus1 j) = j.
Proof.
  intros x j.
  unfold decode_odd_index, boundary, two_j_minus1.
  rewrite (add_sub_cancel_l (B base_params x) (Nat.pred (two j))).
  destruct j as [|j']; [reflexivity|].
  unfold two. replace (S (Nat.pred (S j' + S j'))) with (2 * S j') by lia.
  apply Nat.div2_double.
Qed.

(*@inline@[[Applying the odd-band decoder to each odd-band index inverts the affine reindexing of the encoder, recovering the original Zeckendorf support of the right input.]]@*)

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

(*@inline@[[Summing the normalized even part of the canonical support of an encoded pair reconstructs the left coordinate exactly.]]@*)

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

(*@inline@[[Once the boundary is fixed by the recovered left component, summing the decoded odd support reconstructs the right component exactly.]]@*)

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

(*@inline@[[Concrete roundtrip law: `decode` recovers both coordinates of any pair produced by `encode`.]]@*)

(*@unicodemath@[[∀ a b, decode(encode(a, b)) = (a, b).]]@*)

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

(*@inline@[[Injectivity follows from the roundtrip theorem: equality of codes forces equality of their decoded coordinates, and therefore equality of the original pairs.]]@*)

(*@unicodemath@[[encode(a, b) = encode(a', b') ⇒ a = a' ∧ b = b'.]]@*)

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

(*@inline@[[First projection of the roundtrip law: left-coordinate recovery, recorded as a standalone statement.]]@*)

Corollary decode_encode_fst :
  forall a b, fst (decode (encode a b)) = a.
Proof.
  intros a b.
  rewrite decode_encode.
  reflexivity.
Qed.

(*@inline@[[Second projection of the roundtrip law: right-coordinate recovery, recorded as a standalone statement.]]@*)

Corollary decode_encode_snd :
  forall a b, snd (decode (encode a b)) = b.
Proof.
  intros a b.
  rewrite decode_encode.
  reflexivity.
Qed.

(*@inline@[[A small named instance of the roundtrip theorem at `(1, 1)`.]]@*)

Corollary decode_encode_1_1 :
  decode (encode 1 1) = (1, 1).
Proof. reflexivity. Qed.

(*@inline@[[A small named instance of the roundtrip theorem at `(3, 5)`.]]@*)

Corollary decode_encode_3_5 :
  decode (encode 3 5) = (3, 5).
Proof. reflexivity. Qed.
