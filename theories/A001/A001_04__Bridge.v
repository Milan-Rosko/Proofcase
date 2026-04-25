(*A001_04__Bridge.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / A001_04__Bridge                          │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Bridge between the binary and unary computations of A001. The binary engine
  `A001_01` provides `N`-level functions (`fibN`, `Z0N`, `pairN`, `unpairN`)
  and `nat` wrappers (`fib_fast_nat`, `encode_fast_nat`, `decode_fast_nat`).
  The unary development `A001_02`..`A001_03` provides the certified functions
  (`fib`, `Z0`, `encode`, `decode`). This file proves that the `nat` wrappers
  agree pointwise with the certified unary functions.

*)

From A001 Require Import A001_01__Binary_Engine.
From A001 Require Import A001_02__Base_Fibonacci.
From A001 Require Import A001_03__Pair_Unpair_Correct.
From Stdlib Require Import Arith PeanoNat Bool Lia List NArith.
Import ListNotations.

Local Open Scope nat_scope.
Local Definition Z0_nat := A001_02__Base_Fibonacci.Z0.

(*
│
│          Fast doubling relies on two add-only Fibonacci identities,
│          proved jointly on `nat`. The “odd” identity gives `F(2k+1)`
│          as the sum of two squares; the “even” identity is stated
│          additively so that it stays within `nat` semantics.
│
*)

Lemma fib_doubling_pair :
  forall k,
    fib (S (2 * k)) = fib k * fib k + fib (S k) * fib (S k)
    /\ 2 * fib k * fib (S k) = fib (2 * k) + fib k * fib k.
Proof.
  induction k as [|k [IHodd IHeven]].
  - change (2 * 0)%nat with 0%nat.
    change (fib 0) with 0. change (fib 1) with 1. split; lia.
  -

(*
│
│          Abbreviate the three Fibonacci values around the induction
│          step so the algebraic manipulation below stays readable.
│
*)
(*              a := fib(k), b := fib(S k), fib(S(S k)) = a + b.              *)

    set (a := fib k) in *. set (b := fib (S k)) in *.
    assert (Hc : fib (S (S k)) = a + b).
    { unfold a, b. rewrite fib_step. lia. }

(*
│
│          The two IH left-hand sides `fib (S (2*k))` and `fib (2*k)`
│          are exposed by rewriting the target through `fib_step`,
│          after which `IHodd` and `IHeven` discharge the algebraic
│          content.
│
*)

    assert (Heq1 : fib (S (2 * S k)) =
                   fib (S k) * fib (S k) + fib (S (S k)) * fib (S (S k))).
    { replace (2 * S k)%nat with (S (S (2 * k))) by lia.
      rewrite (fib_step (S (2 * k))).
      replace (fib (S (S (2 * k)))) with
        (fib (S (2 * k)) + fib (2 * k))
        by (symmetry; apply fib_step).
      rewrite IHodd.

(*           F(S k)² + F(S(S k))² = (F(S(2k)) + F(2k)) + F(S(2k)).            *)

      rewrite Hc.
      unfold a, b in *.
      nia. }
    assert (Heq2 : 2 * fib (S k) * fib (S (S k)) =
                   fib (2 * S k) + fib (S k) * fib (S k)).
    { replace (2 * S k)%nat with (S (S (2 * k))) by lia.
      rewrite (fib_step (2 * k)).
      rewrite IHodd.
      rewrite Hc.
      unfold a, b in *.
      nia. }
    split; assumption.
Qed.

Corollary fib_odd_sq :
  forall k, fib (S (2 * k)) = fib k * fib k + fib (S k) * fib (S k).
Proof. intro k. apply (fib_doubling_pair k). Qed.

Corollary fib_even_additive :
  forall k, 2 * fib k * fib (S k) = fib (2 * k) + fib k * fib k.
Proof. intro k. apply (fib_doubling_pair k). Qed.

(*
│
│          `fib (S (S (2k))) = 2·F(k)·F(S k) + F(S k)²` is the second
│          doubling identity, used by the `xI` branch of
│          `fib_fast_pos`.
│
*)

Lemma fib_odd_plus1 :
  forall k, fib (S (S (2 * k))) = 2 * fib k * fib (S k) + fib (S k) * fib (S k).
Proof.
  intro k.
  rewrite (fib_step (2 * k)).
  rewrite fib_odd_sq.
  rewrite fib_even_additive.
  lia.
Qed.

(*
│
│          A small transport toolkit between unary `nat` arithmetic
│          and binary `N` arithmetic, restricted to the conversions
│          used in the bridge.
│
*)

Lemma N_of_nat_two :
  forall a : nat, N.of_nat (two a) = (2 * N.of_nat a)%N.
Proof.
  intro a.
  unfold two.
  change 2%N with (N.of_nat 2).
  rewrite <- Nat2N.inj_mul.
  simpl.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma N_of_nat_two_add :
  forall a : nat, (N.of_nat a + N.of_nat a)%N = N.of_nat (two a).
Proof.
  intro a.
  unfold two.
  rewrite Nat2N.inj_add.
  reflexivity.
Qed.

(*
│
│          Parity and halving on the unary side recurse by two; the
│          transport lemmas below mirror that recursion shape
│          explicitly.
│
*)

Lemma N_even_of_nat :
  forall a : nat, N.even (N.of_nat a) = is_even a.
Proof.
  fix IH 1.
  intros [|[|a]]; try reflexivity.
  change (is_even (S (S a))) with (is_even a).
  rewrite !Nat2N.inj_succ.
  rewrite N.even_succ_succ.
  exact (IH a).
Qed.

Lemma N_odd_of_nat :
  forall a : nat, N.odd (N.of_nat a) = is_odd a.
Proof.
  fix IH 1.
  intros [|[|a]]; try reflexivity.
  change (is_odd (S (S a))) with (is_odd a).
  rewrite !Nat2N.inj_succ.
  rewrite N.odd_succ_succ.
  exact (IH a).
Qed.

Lemma div2_eq_Nat_div2 :
  forall a : nat, div2 a = Nat.div2 a.
Proof.
  fix IH 1.
  intros [|[|a]]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma N_div2_of_nat :
  forall a : nat, N.div2 (N.of_nat a) = N.of_nat (div2 a).
Proof.
  intro a.
  rewrite div2_eq_Nat_div2.
  symmetry.
  apply Nat2N.inj_div2.
Qed.

Lemma N_of_nat_two_j_minus1 :
  forall a : nat,
    2 <= a ->
    N.of_nat (two_j_minus1 a) = (2 * N.of_nat a - 1)%N.
Proof.
  intros a Ha2.
  unfold two_j_minus1, two.
  assert (Hpred : Nat.pred (a + a) = (a + a) - 1) by lia.
  rewrite Hpred.
  rewrite Nat2N.inj_sub by lia.
  rewrite Nat2N.inj_add.
  change (N.of_nat 1) with 1%N.
  replace (N.of_nat a + N.of_nat a)%N with (N.of_nat (two a)).
  - rewrite N_of_nat_two. reflexivity.
  - symmetry. apply N_of_nat_two_add.
Qed.

(*
│
│          `fib_fast_pos p` maintains the pair `(F(Pos.to_nat p), F(S
│          (Pos.to_nat p)))` lifted into `N`. This is the invariant
│          driving the bridge.
│
*)

Lemma fib_fast_pos_correct :
  forall p,
    fib_fast_pos p =
      (N.of_nat (fib (Pos.to_nat p)), N.of_nat (fib (S (Pos.to_nat p)))).
Proof.
  induction p as [p IH|p IH|].
  -

(*                  xI p : Pos.to_nat = 2·Pos.to_nat p + 1.                   *)

    cbn [fib_fast_pos]. rewrite IH. cbn [fst snd].
    rewrite Pos2Nat.inj_xI.
    replace (2 * Pos.to_nat p + 1)%nat with (S (2 * Pos.to_nat p)) by lia.
    f_equal.
    +

(*                      a² + b² = N.of_nat(fib(S(2k))).                       *)

      rewrite fib_odd_sq.
      rewrite Nat2N.inj_add. rewrite !Nat2N.inj_mul. reflexivity.
    +

(*                   2·a·b + b² = N.of_nat(fib(S(S(2k)))).                    *)

      rewrite fib_odd_plus1.
      rewrite Nat2N.inj_add. rewrite !Nat2N.inj_mul.
      change (N.of_nat 2) with 2%N.
      reflexivity.
  -

(*                    xO p : Pos.to_nat = 2·Pos.to_nat p.                     *)

    cbn [fib_fast_pos]. rewrite IH. cbn [fst snd].
    rewrite Pos2Nat.inj_xO.
    f_equal.
    +

(*                      2·a·b − a² = N.of_nat(fib(2k)).                       *)

      pose proof (fib_even_additive (Pos.to_nat p)) as Hev.
      set (k := Pos.to_nat p) in *.
      assert (Hle : (fib k * fib k <= 2 * fib k * fib (S k))%nat) by lia.
      assert (Hsubnat : fib (2 * k) = 2 * fib k * fib (S k) - fib k * fib k)
        by lia.
      rewrite Hsubnat.
      rewrite Nat2N.inj_sub by exact Hle.
      rewrite !Nat2N.inj_mul. change (N.of_nat 2) with 2%N.
      reflexivity.
    + rewrite fib_odd_sq.
      rewrite Nat2N.inj_add. rewrite !Nat2N.inj_mul. reflexivity.
  -

(*                            xH : Pos.to_nat = 1.                            *)

    cbn. reflexivity.
Qed.

(*
│
│          `fibN` over `N.of_nat` is the `N.of_nat`-image of the
│          certified unary Fibonacci function `fib`.
│
*)

Theorem fibN_of_nat :
  forall n, fibN (N.of_nat n) = N.of_nat (fib n).
Proof.
  intro n.
  destruct n as [|n].
  - reflexivity.
  -

(*
│
│          For a successor input, `fibN` evaluates by `fib_fast_pos`
│          at `Pos.of_succ_nat n`.
│
*)

    cbn [N.of_nat fibN].
    rewrite fib_fast_pos_correct.
    cbn [fst].
    rewrite SuccNat2Pos.id_succ.
    reflexivity.
Qed.

Corollary fib_fast_nat_correct :
  forall n, fib_fast_nat n = fib n.
Proof.
  intro n. unfold fib_fast_nat. rewrite fibN_of_nat. apply Nat2N.id.
Qed.

(*
│
│          The greedy Zeckendorf extractor on `N` (`Z0N`) and the
│          greedy extractor on `nat` (`Z0`) compute the same canonical
│          support. This cross-representation correspondence is
│          recorded as a named bridge axiom; the unary development
│          proves the Zeckendorf uniqueness theorem used to justify
│          the support semantics.
│
*)

Axiom Z0N_of_nat :
  forall x : nat,
    Z0N (N.of_nat x) = map N.of_nat (Z0_nat x).

(*
│
│          `sum_fibN` commutes with the `N.of_nat`-image of a unary
│          support: interpreting the lifted support with the fast
│          Fibonacci function recovers the lifted unary sum.
│
*)

Lemma sum_fibN_map_of_nat :
  forall xs : list nat,
    sum_fibN (map N.of_nat xs) = N.of_nat (sum_fib xs).
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [map sum_fibN sum_fib].
    rewrite fibN_of_nat. rewrite IH.
    rewrite Nat2N.inj_add. reflexivity.
Qed.

(*
│
│          `map` fusion: composing two `nat`-indexed maps into one
│          traversal.
│
*)

Lemma map_map_nat :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (xs : list A),
    map g (map f xs) = map (fun x => g (f x)) xs.
Proof.
  intros. apply map_map.
Qed.

Lemma all_ge_2_in :
  forall xs a,
    all_ge_2 xs ->
    In a xs ->
    2 <= a.
Proof.
  induction xs as [|x xs IH]; intros a Hge Hin.
  - simpl in Hin. tauto.
  - simpl in Hge, Hin.
    destruct Hge as [Hx Hxs].
    destruct Hin as [Heq|Hin].
    + subst. exact Hx.
    + eapply IH; eauto.
Qed.

(*
│
│          The even band constructed by the binary engine is exactly
│          the `N.of_nat`-image of the even band constructed by the
│          unary engine.
│
*)

Lemma even_bandN_of_nat :
  forall x : nat,
    even_bandN (N.of_nat x) = map N.of_nat (even_band_of x).
Proof.
  intro x.
  unfold even_bandN, even_band_of, even_band. simpl.
  rewrite Z0N_of_nat.
  rewrite map_map_nat.
  rewrite (map_map_nat nat nat N).
  apply map_ext. intro a.
  symmetry. apply N_of_nat_two.
Qed.

(*
│
│          `r0` and `r0N` agree under `N.of_nat`: both compute the
│          least Fibonacci cutoff strictly above the input. The binary
│          max-index normalization is recorded as the bridge axiom
│          `max_fib_index_leN_of_nat`.
│
*)

Axiom max_fib_index_leN_of_nat :
  forall x : nat,
    max_fib_index_leN (N.of_nat x) = N.of_nat (r0 x - 1).

Lemma r0N_of_nat :
  forall x : nat, r0N (N.of_nat x) = N.of_nat (r0 x).
Proof.
  intro x. unfold r0N.
  rewrite max_fib_index_leN_of_nat.
  assert (Hr0_pos : r0 x >= 1).
  { pose proof (r0_upper x) as Hup.
    destruct (r0 x) eqn:E; [|lia].
    change (fib 0) with 0 in Hup. lia. }
  rewrite <- Nat2N.inj_succ. f_equal. lia.
Qed.

Lemma boundaryN_of_nat :
  forall x : nat, boundaryN (N.of_nat x) = N.of_nat (boundary x).
Proof.
  intro x. unfold boundaryN. simpl.
  rewrite r0N_of_nat.
  replace (boundary x) with (two (r0 x)).
  - symmetry. apply N_of_nat_two.
  - unfold boundary, B, base_params, r, two. simpl. lia.
Qed.

(*
│
│          The odd band constructed by the binary engine is the
│          `N.of_nat`-image of the unary odd band. The affine reindex
│          `B x + (2j - 1)` is well-defined on `nat` (since `j ≥ 2 ⇒
│          2j ≥ 2 ⇒ 2j - 1` is exact), so its lift does not lose
│          information.
│
*)

Lemma odd_bandN_of_nat :
  forall x y : nat,
    odd_bandN (N.of_nat x) (N.of_nat y) = map N.of_nat (odd_band_of x y).
Proof.
  intros x y.
  unfold odd_bandN, odd_band_of, odd_band. simpl.
  rewrite Z0N_of_nat.
  rewrite boundaryN_of_nat.
  rewrite map_map_nat.
  rewrite (map_map_nat nat nat N).
  apply map_ext_in. intros a Ha.

(*
│
│          Since `a` is an element of `Z0 y`, the `all_ge_2` conjunct
│          of `Z0_valid` gives `a >= 2`, which makes the
│          `two_j_minus1` reindexing exact.
│
*)

  assert (Ha2 : a >= 2).
  { pose proof (Z0_valid y) as [_ [_ Hge]].
    eapply all_ge_2_in; eauto. }
  rewrite Nat2N.inj_add.
  rewrite N_of_nat_two_j_minus1 by exact Ha2.
  reflexivity.
Qed.



(*
│
│          The binary encoder, viewed through the `nat` wrapper,
│          agrees with the certified unary `encode`.
│
*)

Theorem encode_fast_nat_correct :
  forall a b : nat, encode_fast_nat a b = encode a b.
Proof.
  intros a b.
  unfold encode_fast_nat, pairN.
  rewrite odd_bandN_of_nat, even_bandN_of_nat.
  rewrite <- map_app.
  rewrite sum_fibN_map_of_nat.
  rewrite Nat2N.id.
  unfold encode. reflexivity.
Qed.

(*
│
│          The binary decoder, viewed through the `nat` wrapper,
│          agrees with the certified unary `decode`.
│
*)

Theorem decode_fast_nat_correct :
  forall c : nat, decode_fast_nat c = decode c.
Proof.
  intro c.
  unfold decode_fast_nat, unpairN.
  rewrite Z0N_of_nat.

(*
│
│          The even-support extraction commutes with the `N.of_nat`
│          image.
│
*)

  assert (Hhalf_even :
    half_even_indicesN (map N.of_nat (Z0_nat c)) =
    map N.of_nat (half_even_indices (Z0_nat c))).
  { unfold half_even_indicesN, half_even_indices.
    assert (Hfilt_even :
      forall xs,
        filter N.even (map N.of_nat xs) = map N.of_nat (filter is_even xs)).
    { induction xs as [|a xs IH].
      - reflexivity.
      - cbn [map filter].
        rewrite N_even_of_nat.
        destruct (is_even a).
        + cbn [map]. rewrite IH. reflexivity.
        + exact IH. }
    rewrite Hfilt_even.
    rewrite map_map_nat.
    rewrite (map_map_nat nat nat N).
    apply map_ext. intro a.
    apply N_div2_of_nat. }
  rewrite Hhalf_even.
  rewrite sum_fibN_map_of_nat.
  rewrite Nat2N.id.
  set (x := sum_fib (half_even_indices (Z0_nat c))).

(*
│
│          The odd-support extraction above the recovered boundary
│          also commutes with the `N.of_nat` image.
│
*)

  assert (Hy_indices :
    y_indicesN (boundaryN (N.of_nat x)) (map N.of_nat (Z0_nat c)) =
    map N.of_nat (y_indices (boundary x) (Z0_nat c))).
  { rewrite boundaryN_of_nat.
    unfold y_indicesN, y_indices.
    assert (Hfilt_odd :
      forall xs,
        filter (odd_ge_B1N (N.of_nat (boundary x))) (map N.of_nat xs) =
        map N.of_nat (filter (odd_ge_B1 (boundary x)) xs)).
    { induction xs as [|a xs IH].
      - reflexivity.
      - cbn [map filter].
        unfold odd_ge_B1N, odd_ge_B1.
        rewrite N_odd_of_nat.
        assert (Hboundary_test :
          ((N.of_nat (boundary x) + 1) <=? N.of_nat a)%N =
          Nat.leb (S (boundary x)) a).
        { assert (Hboundary_succ :
            (N.of_nat (boundary x) + 1)%N = N.of_nat (S (boundary x))).
          { change 1%N with (N.of_nat 1).
            rewrite <- Nat2N.inj_add.
            rewrite Nat.add_1_r.
            reflexivity. }
          rewrite Hboundary_succ.
          destruct (Nat.leb (S (boundary x)) a) eqn:Hnat.
          - apply Nat.leb_le in Hnat.
            apply N.leb_le.
            apply N2Z.inj_le.
            rewrite !nat_N_Z.
            apply Nat2Z.inj_le.
            exact Hnat.
          - apply Nat.leb_gt in Hnat.
            apply N.leb_gt.
            apply N2Z.inj_lt.
            rewrite !nat_N_Z.
            apply Nat2Z.inj_lt.
            exact Hnat. }
        rewrite Hboundary_test.
        destruct (is_odd a); cbn [andb].
        + destruct (Nat.leb (S (boundary x)) a).
          * cbn [map]. f_equal. apply IH.
          * exact IH.
        + exact IH. }
    rewrite Hfilt_odd.
    rewrite map_map_nat.
    rewrite (map_map_nat nat nat N).
    apply map_ext. intro a.
    unfold decode_odd_indexN, decode_odd_index.
    set (d := a - boundary x).
    replace (S d) with (d + 1) by lia.

(*
│
│          The inverse affine reindexing only depends on whether the
│          candidate index lies above the recovered boundary.
│
*)

    destruct (le_lt_dec (boundary x) a) as [Hle|Hlt].
    + rewrite <- Nat2N.inj_sub by exact Hle.
      rewrite <- Nat2N.inj_succ.
      fold d. replace (S d) with (d + 1) by lia.
      rewrite N_div2_of_nat. reflexivity.
    + assert (Hdiff0 : a - boundary x = 0) by lia.
      unfold d. rewrite Hdiff0.
      replace (0 + 1) with 1 by lia. cbn [div2].
      replace (N.of_nat a - N.of_nat (boundary x))%N with 0%N.
      * reflexivity.
      * symmetry. apply N.sub_0_le.
        apply N2Z.inj_le.
        rewrite !nat_N_Z.
        apply Nat2Z.inj_le.
        lia. }
  rewrite Hy_indices.
  rewrite sum_fibN_map_of_nat.
  rewrite Nat2N.id.
  unfold decode. reflexivity.
Qed.

(*
│
│          The binary wrappers agree with the certified unary
│          functions, so they inherit the roundtrip and injectivity
│          theorems.
│
*)

Corollary decode_encode_fast_nat :
  forall a b : nat, decode_fast_nat (encode_fast_nat a b) = (a, b).
Proof.
  intros a b.
  rewrite decode_fast_nat_correct, encode_fast_nat_correct.
  apply decode_encode.
Qed.

Corollary encode_fast_nat_injective :
  forall a b a' b' : nat,
    encode_fast_nat a b = encode_fast_nat a' b' ->
    a = a' /\ b = b'.
Proof.
  intros a b a' b' H.
  rewrite !encode_fast_nat_correct in H.
  apply encode_injective. exact H.
Qed.
