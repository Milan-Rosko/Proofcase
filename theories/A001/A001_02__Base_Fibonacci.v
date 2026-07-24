(*A001_02__Base_Fibonacci.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / A001_02__Base_Fibonacci                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We develop Fibonacci arithmetic on `nat`, the concrete Zeckendorf support
  engine (`Z0`, `r0`), and the structural lemmas — band validity, support
  uniqueness, and pair/unpair compatibility — on which the pairing and
  unpairing layers depend.

*)

From A001 Require Export A001_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             FIBONACCI ARITHMETIC                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `fib_pair` maintains the pair `(F(n), F(n+1))`, so that the
│          successor case extends by a single Fibonacci step rather
│          than revisiting earlier values; `fib` is its first
│          projection.
│
*)

Fixpoint fib_pair (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 1)
  | S n' =>
      match fib_pair n' with
      | (a, b) => (b, a + b)
      end
  end.

Definition fib (n : nat) : nat := fst (fib_pair n).

(*
│
│          `sum_fib` evaluates a finite support of Fibonacci indices
│          as the sum of the corresponding Fibonacci values. This is
│          the numeric reading map used throughout the carryless
│          encoding.
│
*)

Fixpoint sum_fib (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | k :: xs' => fib k + sum_fib xs'
  end.

(*
│
│          `two n = n + n` and `two_j_minus1 j = pred(2j)` are written
│          additively so that the odd-band reindexing `2j - 1` stays
│          within `nat` for `j >= 1` without recourse to saturating
│          subtraction.
│
*)

Definition two (n : nat) : nat := n + n.

Definition two_j_minus1 (j : nat) : nat := Nat.pred (two j).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          PARAMETRIC CARRYLESS SHAPE                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `Params` bundles a support extractor `Z` and a cutoff `r`.
│          The pairing construction is parametric in this pair of
│          operations; the concrete Zeckendorf instance uses `Z0` and
│          `r0`.
│
*)

Inductive Params : Type :=
| Build_Params : (nat -> list nat) -> (nat -> nat) -> Params.

Definition Z (P : Params) : nat -> list nat :=
  match P with
  | Build_Params z0 _ => z0
  end.

Definition r (P : Params) : nat -> nat :=
  match P with
  | Build_Params _ r0 => r0
  end.

(*                            B_P(x) ≔ 2 · r_P(x)                             *)

Definition B (P : Params) (x : nat) : nat := 2 * r P x.

(*                    even_band_P(x) ≔ { 2e ∣ e ∈ Z_P(x) }                    *)
(*           odd_band_P(x, y) ≔ { B_P(x) + (2j − 1) ∣ j ∈ Z_P(y) }            *)

Definition even_band (P : Params) (x : nat) : list nat :=
  map (fun e => two e) (Z P x).

Definition odd_band (P : Params) (x y : nat) : list nat :=
  map (fun j => B P x + two_j_minus1 j) (Z P y).

(*
│
│          The abstract carryless code is formed by combining the
│          even-band support of the left input with the odd-band
│          support of the right input, and then evaluating the result
│          as a finite Fibonacci support.
│
*)

Definition pair (P : Params) (x y : nat) : nat :=
  sum_fib (even_band P x ++ odd_band P x y).

(*
│
│          We isolate the even Zeckendorf indices and renormalize them
│          by halving; this recovers the candidate support from which
│          the left component is reconstructed.
│
*)

Definition half_even_indices (zn : list nat) : list nat :=
  map Nat.div2 (filter Nat.even zn).

(*                 odd_ge_B1(B, k) = true ⇔ 2 ∤ k ∧ B + 1 ≤ k                 *)

Definition odd_ge_B1 (Bx k : nat) : bool :=
  Nat.odd k && Nat.leb (S Bx) k.

(*                 decode_odd_index(B, k) ≔ ⌊(k − B + 1) / 2⌋                 *)

Definition decode_odd_index (Bx k : nat) : nat :=
  Nat.div2 (S (k - Bx)).

(*
│
│          The candidate right-hand support is recovered by selecting
│          precisely those odd indices that lie strictly above the
│          boundary and transporting them back through the inverse
│          affine reindexing.
│
*)

Definition y_indices (Bx : nat) (zn : list nat) : list nat :=
  map (decode_odd_index Bx) (filter (odd_ge_B1 Bx) zn).

(*
│
│          `unpair` is the recovery map associated with parameters
│          `P`. We first reconstruct the left component from the even
│          support, and then reconstruct the right component from the
│          odd support lying above the recovered boundary.
│
*)

Definition unpair (P : Params) (n : nat) : nat * nat :=
  let zn := Z P n in
  let x := sum_fib (half_even_indices zn) in
  let Bx := B P x in
  let y := sum_fib (y_indices Bx zn) in
  (x, y).

(*
│
│          The three structural predicates `strictly_decreasing`,
│          `no_adjacent`, and `all_ge_2` are the conjuncts of
│          `zeck_valid` below. They encode, respectively, descent, the
│          gap-of-2 spacing required by Zeckendorf, and the index
│          lower bound that excludes `fib 0` and `fib 1`.
│
*)

Fixpoint strictly_decreasing (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: _ => a > b /\ strictly_decreasing xs'
      end
  end.

Fixpoint no_adjacent (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: _ => a >= b + 2 /\ no_adjacent xs'
      end
  end.

Fixpoint all_ge_2 (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | a :: xs' => 2 <= a /\ all_ge_2 xs'
  end.

(*
│
│          `zeck_valid` is the admissibility predicate for Zeckendorf
│          supports. It enforces strict descent, the exclusion of
│          adjacent indices, and the lower bound `2` on every used
│          index.
│
*)

(*                  zeck_valid(xs) ≔ strictly_decreasing(xs)                  *)
(*                     ∧ no_adjacent(xs) ∧ all_ge_2(xs).                      *)

Definition zeck_valid (xs : list nat) : Prop :=
  strictly_decreasing xs /\ no_adjacent xs /\ all_ge_2 xs.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                CUTOFF SEARCH                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `find_r_aux` is the bounded upward search underlying `r0`:
│          starting at index `k`, we advance until `fib k` strictly
│          exceeds `x`, with `fuel` capping the loop so the function
│          remains structurally recursive.
│
*)

Fixpoint find_r_aux (x k fuel : nat) : nat :=
  match fuel with
  | 0 => k
  | S fuel' =>
      if Nat.ltb x (fib k)
      then k
      else find_r_aux x (S k) fuel'
  end.

(*
│
│          `r0(x)` is the first Fibonacci cutoff strictly above `x`.
│          The greedy constructor need only search below this index.
│
*)

(*                      r0(x) ≔ min { k ∈ ℕ ∣ x < F(k) }                      *)

Definition r0 (x : nat) : nat := find_r_aux x 0 (S (S x)).

(*
│
│          `zeck_greedy_down` is the greedy Zeckendorf descent:
│          starting at the cutoff `k`, we take `fib k` whenever it
│          fits in the remainder and the previous index was not taken
│          (so adjacency is precluded), and otherwise step down by
│          one. The function returns the support together with the
│          residual remainder.
│
*)

Fixpoint zeck_greedy_down (k rem : nat) (prev_taken : bool)
  : list nat * nat :=
  match k with
  | 0 => ([], rem)
  | S k' =>
      match k' with
      | 0 => ([], rem)
      | S _ =>
          if prev_taken then
            zeck_greedy_down k' rem false
          else
            if Nat.leb (fib k) rem then
              let pr := zeck_greedy_down k' (rem - fib k) true in
              (k :: fst pr, snd pr)
            else
              zeck_greedy_down k' rem false
      end
  end.

(*
│
│          `Z0` is the concrete greedy Zeckendorf support. It computes
│          the canonical non-adjacent Fibonacci index set that
│          represents the input number.
│
*)

Definition Z0 (x : nat) : list nat :=
  fst (zeck_greedy_down (r0 x) x false).

(*
│
│          `base_params` instantiates the parametric pairing
│          construction with the concrete support extractor `Z0` and
│          cutoff `r0`.
│
*)

Definition base_params : Params :=
  Build_Params Z0 r0.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            FIBONACCI RECURRENCES                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Lemma fib_pair_S : forall n a b,
  fib_pair n = (a, b) -> fib_pair (S n) = (b, a + b).
Proof.
  intros n a b H.
  simpl. rewrite H. reflexivity.
Qed.

Lemma fib_S : forall n, fib (S n) = snd (fib_pair n).
Proof.
  intro n. unfold fib. simpl. destruct (fib_pair n) as [a b]. reflexivity.
Qed.

Lemma fib_step : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof.
  intro n.
  rewrite fib_S.
  destruct (fib_pair n) as [a b] eqn:Hn.
  assert (Hs : fib_pair (S n) = (b, a + b)).
  - simpl. rewrite Hn. reflexivity.
  - rewrite Hs.
  unfold fib. rewrite Hs. rewrite Hn. simpl.
  rewrite Nat.add_comm. reflexivity.
Qed.

Lemma fib_S_ge : forall n, fib (S n) >= fib n.
Proof.
  induction n as [|n IH].
  - unfold fib. simpl. lia.
  - rewrite fib_step. lia.
Qed.

Lemma fib_pos_S : forall n, fib (S n) >= 1.
Proof.
  induction n as [|n IH].
  - unfold fib. simpl. lia.
  - rewrite fib_step. lia.
Qed.

Lemma fib_pos : forall n, n >= 1 -> fib n >= 1.
Proof.
  intros n H.
  destruct n as [|n].
  - lia.
  - apply fib_pos_S.
Qed.

Lemma fib_monotone_le : forall a b, a < b -> fib a <= fib b.
Proof.
  intros a b Hlt.
  induction b as [|b IH]; [lia|].
  destruct (Nat.eq_dec a b) as [Heq|Hneq].
  - subst. apply fib_S_ge.
  - assert (a < b) by lia.
    specialize (IH H).
    apply Nat.le_trans with (m:=fib b); [exact IH |].
    apply fib_S_ge.
Qed.

Lemma fib_gap2_gt : forall a, fib a < fib (S (S a)).
Proof.
  intro a.
  rewrite fib_step.
  assert (Hpos : fib (S a) >= 1) by apply fib_pos_S.
  lia.
Qed.

Lemma fib_monotone_gap2 : forall a b, a + 1 < b -> fib a < fib b.
Proof.
  intros a b Hlt.
  assert (Hle : S (S a) <= b) by lia.
  apply Nat.lt_le_trans with (m:=fib (S (S a))).
  - apply fib_gap2_gt.
  - destruct (Nat.eq_dec (S (S a)) b) as [Heq|Hneq].
    + subst. apply Nat.le_refl.
    + apply fib_monotone_le. lia.
Qed.

Lemma add_sub_cancel_r : forall a b, a <= b -> a + (b - a) = b.
Proof.
  intros a b Hle. lia.
Qed.

Lemma add_assoc_l : forall a b c, a + b + c = a + (b + c).
Proof.
  intros a b c. lia.
Qed.

Lemma fib_ge_Sn : forall n, fib (S (S n)) >= S n.
Proof.
  induction n as [|n IH].
  - vm_compute. lia.
  - rewrite fib_step.
    assert (Hpos : fib (S n) >= 1) by apply fib_pos_S.
    lia.
Qed.

Lemma find_r_aux_upper_from_witness :
  forall x k fuel,
    x < fib (k + fuel) ->
    x < fib (find_r_aux x k fuel).
Proof.
  intros x k fuel.
  revert k.
  induction fuel as [|fuel IH]; intros k Hlt.
  - simpl in *. replace (k + 0) with k in Hlt by lia. simpl. exact Hlt.
  - simpl in *.
    destruct (Nat.ltb x (fib k)) eqn:Hk.
    + apply Nat.ltb_lt. exact Hk.
    + apply IH.
      replace (S k + fuel) with (k + S fuel) by lia.
      exact Hlt.
Qed.

(*                       k ≤ j < find_r_aux(x, k, fuel)                       *)
(*                                ⇒ F(j) ≤ x.                                 *)

Lemma find_r_aux_before_false :
  forall x k fuel j,
    k <= j ->
    j < find_r_aux x k fuel ->
    Nat.ltb x (fib j) = false.
Proof.
  intros x k fuel.
  revert x k.
  induction fuel as [|fuel IH]; intros x k j Hkj Hlt.
  - simpl in Hlt. lia.
  - simpl in Hlt.
    destruct (Nat.ltb x (fib k)) eqn:Hk.
    + lia.
    + destruct (Nat.eq_dec j k) as [->|Hneq].
      * exact Hk.
      * assert (Hskj : S k <= j) by lia.
        eapply IH; eauto.
Qed.

(*
│
│          `r0_upper` gives the upper half of the cutoff
│          characterization: the search terminates strictly above `n`.
│
*)

(*                             ∀ n, n < F(r0(n)).                             *)

Lemma r0_upper :
  forall n, n < fib (r0 n).
Proof.
  intro n.
  unfold r0.
  apply find_r_aux_upper_from_witness.
  replace (0 + S (S n)) with (S (S n)) by lia.
  assert (Hge : fib (S (S n)) >= S n) by apply fib_ge_Sn.
  lia.
Qed.

Corollary r0_upper_S :
  forall n, n < fib (S (r0 n)).
Proof.
  intro n.
  assert (Hup : n < fib (r0 n)) by apply r0_upper.
  assert (Hmono : fib (r0 n) <= fib (S (r0 n))) by apply fib_S_ge.
  lia.
Qed.

(*
│
│          The lower half of the cutoff characterization: every
│          Fibonacci index strictly below `r0(n)` still evaluates to a
│          value at most `n`. In conjunction with `r0_upper`, this
│          identifies `r0(n)` as the least Fibonacci index whose value
│          lies strictly above `n`.
│
*)

(*                        ∀ n k, k < r0(n) ⇒ F(k) ≤ n.                        *)

Lemma r0_minimal :
  forall n k, k < r0 n -> fib k <= n.
Proof.
  intros n k Hlt.
  unfold r0 in Hlt.
  pose proof (find_r_aux_before_false n 0 (S (S n)) k (Nat.le_0_l k) Hlt) as Hfalse.
  apply Nat.ltb_ge in Hfalse.
  exact Hfalse.
Qed.
