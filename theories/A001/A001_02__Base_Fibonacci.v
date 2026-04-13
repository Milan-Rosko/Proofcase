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

  The present construction constitutes full arithmetic base of A001. It
  contains the Fibonacci arithmetic, the concrete Zeckendorf support engine,
  and the structural lemmas later used by the pairing and unpairing layers.

*)

From Stdlib Require Export Arith PeanoNat Bool Lia List Ring ZArith Extraction.
From A001 Require Import A001_01__Binary_Engine.
Export ListNotations.
Global Open Scope list_scope.

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
│          by summing the corresponding Fibonacci values. This is the
│          numeric reading map used throughout the “carryless”
│          encoding.
│
*)

Fixpoint sum_fib (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | k :: xs' => fib k + sum_fib xs'
  end.

Definition two (n : nat) : nat := n + n.

Definition two_j_minus1 (j : nat) : nat := Nat.pred (two j).

Fixpoint is_even (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S k) => is_even k
  end.

Definition is_odd (n : nat) : bool := negb (is_even n).

Fixpoint div2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S k) => S (div2 k)
  end.

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

(*                             B_P(x) = 2·r_P(x)                              *)

Definition B (P : Params) (x : nat) : nat := 2 * r P x.

(*                     even_band_P(x) = {2e ∣ e ∈ Z_P(x)}                     *)
(*            odd_band_P(x, y) = {B_P(x) + (2j − 1) ∣ j ∈ Z_P(y)}             *)

Definition even_band (P : Params) (x : nat) : list nat :=
  map (fun e => two e) (Z P x).

Definition odd_band (P : Params) (x y : nat) : list nat :=
  map (fun j => B P x + two_j_minus1 j) (Z P y).

(*
│
│          We form the abstract “carryless” code by taking the
│          even-band support of the left input together with the
│          odd-band support of the right input and then evaluating the
│          resulting finite Fibonacci support.
│
*)

Definition pair (P : Params) (x y : nat) : nat :=
  sum_fib (even_band P x ++ odd_band P x y).

(*
│
│          We isolate the even Zeckendorf indices and renormalize them
│          by halving, thereby recovering the candidate support from
│          which the left component will be reconstructed.
│
*)

Definition half_even_indices (zn : list nat) : list nat :=
  map div2 (filter is_even zn).

(*                 odd_ge_B1(B, k) = true ⇔ 2 ∤ k ∧ B + 1 ≤ k                 *)

Definition odd_ge_B1 (Bx k : nat) : bool :=
  match is_odd k with
  | false => false
  | true => Nat.leb (S Bx) k
  end.

(*                  decode_odd_index(B, k) = ⌊(k − B + 1)/2⌋                  *)

Definition decode_odd_index (Bx k : nat) : nat :=
  div2 (S (k - Bx)).

(*
│
│          We recover the candidate right-hand support by selecting
│          exactly those odd indices that lie strictly above the
│          boundary and transporting them back through the inverse
│          affine reindexing.
│
*)

Definition y_indices (Bx : nat) (zn : list nat) : list nat :=
  map (decode_odd_index Bx) (filter (odd_ge_B1 Bx) zn).

(*
│
│          `unpair` is the abstract recovery map attached to a
│          parameter package `P`. It reconstructs the left component
│          from the even support and then reconstructs the right
│          component from the odd support above the recovered
│          boundary.
│
*)

Definition unpair (P : Params) (n : nat) : nat * nat :=
  let zn := Z P n in
  let x := sum_fib (half_even_indices zn) in
  let Bx := B P x in
  let y := sum_fib (y_indices Bx zn) in
  (x, y).

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
│          supports. It enforces strict descent, exclusion of adjacent
│          indices, and the lower bound `2` on all used indices.
│
*)

(*                  zeck_valid(xs) ≔ strictly_decreasing(xs)                  *)
(*                     ∧ no_adjacent(xs) ∧ all_ge_2(xs).                      *)

Definition zeck_valid (xs : list nat) : Prop :=
  strictly_decreasing xs /\ no_adjacent xs /\ all_ge_2 xs.

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
│          The greedy constructor only needs to search below this
│          index.
│
*)

(*                      r0(x) = min{k ∈ ℕ ∣ x < fib(k)}                       *)

Definition r0 (x : nat) : nat := find_r_aux x 0 (S (S x)).

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
│          the canonical non-adjacent Fibonacci index set that later
│          feeds the pairing and decoding layers.
│
*)

Definition Z0 (x : nat) : list nat :=
  fst (zeck_greedy_down (r0 x) x false).

(*
│
│          We now fix the distinguished parameter package by pairing
│          the concrete greedy support extractor with its associated
│          cutoff function; all subsequent concrete pairing statements
│          specialize the abstract interface to this package.
│
*)

Definition base_params : Params :=
  Build_Params Z0 r0.

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
(*                               ⇒ fib(j) ≤ x.                                *)

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
│          characterization: the search really stops above `n`.
│
*)

(*                            ∀ n, n < fib(r0(n)).                            *)

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
│          We obtain the lower half of the cutoff characterization as
│          well: every Fibonacci index strictly below `r0(n)` still
│          evaluates to a value at most `n`.
│
*)

(*
│
│          r0(n) is the least Fibonacci index whose value lies
│          strictly above n.
│
*)

(*                           k < r0(n) ⇒ fib(k) ≤ n                           *)

Lemma r0_minimal :
  forall n k, k < r0 n -> fib k <= n.
Proof.
  intros n k Hlt.
  unfold r0 in Hlt.
  pose proof (find_r_aux_before_false n 0 (S (S n)) k (Nat.le_0_l k) Hlt) as Hfalse.
  apply Nat.ltb_ge in Hfalse.
  exact Hfalse.
Qed.

Fixpoint all_le (m : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => x <= m /\ all_le m xs'
  end.

Definition bound (k : nat) (prev_taken : bool) : nat :=
  if prev_taken then Nat.pred k else k.

Lemma all_le_weaken : forall m n xs,
  all_le m xs -> m <= n -> all_le n xs.
Proof.
  induction xs as [|x xs IH]; intros Hle Hmn; simpl in *; auto.
  destruct Hle as [Hx Hxs].
  split; [lia | exact (IH Hxs Hmn)].
Qed.

Lemma zeck_valid_cons_ge2 :
  forall m xs,
    zeck_valid xs ->
    all_le m xs ->
    zeck_valid (S (S m) :: xs).
Proof.
  intros m xs [Hdec [Hadj Hge]] Hall.
  split; [|split].
  - destruct xs as [|x xs']; simpl; auto.
    destruct Hall as [Hx Hall'].
    split; [lia | exact Hdec].
  - destruct xs as [|x xs']; simpl; auto.
    destruct Hall as [Hx Hall'].
    split; [lia | exact Hadj].
  - simpl. split; [lia | exact Hge].
Qed.

(*
│
│          `greedy_inv` packages the greedy correctness invariant: xs
│          encodes the extracted support, rem' is the leftover
│          remainder, xs stays within the current bound, and the
│          remainder remains below the next admissible Fibonacci
│          threshold.
│
*)

Definition greedy_inv k rem prev_taken xs rem' :=
  sum_fib xs + rem' = rem /\
  zeck_valid xs /\
  all_le (bound k prev_taken) xs /\
  (k <= 1 -> xs = [] /\ rem' = rem) /\
  (rem < fib (S (bound k prev_taken)) -> rem' < fib (S (bound k prev_taken))).

Lemma greedy_take_step_sum :
  forall k rem xs rem',
    fib k <= rem ->
    sum_fib xs + rem' = rem - fib k ->
    sum_fib (k :: xs) + rem' = rem.
Proof.
  intros k rem xs rem' Hle Hsum.
  simpl.
  rewrite <- Nat.add_assoc.
  rewrite Hsum.
  apply add_sub_cancel_r.
  exact Hle.
Qed.

(*
│
│          `zeck_greedy_down_correct_core` is the main recursive
│          engine lemma. It shows that every branch of the greedy
│          descent produces a support/remainder pair satisfying the
│          full invariant package `greedy_inv`.
│
*)

(*                zeck_greedy_down(k, rem, prev) = (xs, rem')                 *)
(*                   ⇒ greedy_inv(k, rem, prev, xs, rem').                    *)

Lemma zeck_greedy_down_correct_core :
  forall k rem prev_taken xs rem',
    zeck_greedy_down k rem prev_taken = (xs, rem') ->
    greedy_inv k rem prev_taken xs rem'.
Proof.
  induction k as [|k IH]; intros rem prev xs rem' H.
  - simpl in H. inversion H; subst.
    assert (Hsum : sum_fib [] + rem' = rem') by (simpl; lia).
    assert (Hz : zeck_valid []) by (simpl; split; [exact I|]; split; exact I).
    assert (Hall : all_le (bound 0 prev) []) by (simpl; exact I).
    assert (Hlow : 0 <= 1 -> ([] : list nat) = [] /\ rem' = rem')
      by (intros _; split; reflexivity).
    assert (Hbd : rem' < fib (S (bound 0 prev)) -> rem' < fib (S (bound 0 prev)))
      by (intro Hrem; exact Hrem).
    exact (conj Hsum (conj Hz (conj Hall (conj Hlow Hbd)))).
  - destruct k as [|k']; simpl in H.
    + simpl in H.
      inversion H; subst.
      assert (Hsum : sum_fib [] + rem' = rem') by (simpl; lia).
      assert (Hz : zeck_valid []) by (simpl; split; [exact I|]; split; exact I).
      assert (Hall : all_le (bound 1 prev) []) by (simpl; exact I).
      assert (Hlow : 1 <= 1 -> ([] : list nat) = [] /\ rem' = rem')
        by (intros _; split; reflexivity).
      assert (Hbd : rem' < fib (S (bound 1 prev)) -> rem' < fib (S (bound 1 prev)))
        by (intro Hrem; exact Hrem).
      exact (conj Hsum (conj Hz (conj Hall (conj Hlow Hbd)))).
    + destruct prev eqn:Hprev.
      * specialize (IH rem false xs rem' H) as [Hsum [Hz [Hall [Hlow Hbd]]]].
        refine (conj Hsum (conj Hz (conj _ (conj _ _))));
          [simpl; exact Hall | intros Hk; lia | intros Hrem; lia].
      * destruct (Nat.leb (fib (S (S k'))) rem) eqn:Hle.
        -- destruct (zeck_greedy_down (S k') (rem - fib (S (S k'))) true)
             as [xs' rem''] eqn:Hpr.
           change
             ((S (S k')
               :: fst (zeck_greedy_down (S k') (rem - fib (S (S k'))) true),
               snd (zeck_greedy_down (S k') (rem - fib (S (S k'))) true))
              = (xs, rem')) in H.
           rewrite Hpr in H.
           inversion H; subst xs rem'. clear H.
           specialize (IH (rem - fib (S (S k'))) true xs' rem'' Hpr)
             as [Hsum [Hz [Hall [Hlow Hbd]]]].
           refine (conj _ (conj _ (conj _ (conj _ _))));
             [ apply Nat.leb_le in Hle;
               eapply greedy_take_step_sum; [exact Hle | exact Hsum]
             | simpl in Hall; apply (zeck_valid_cons_ge2 k' xs'); assumption
             | simpl; split; [lia|]; apply all_le_weaken with (m:=k'); [exact Hall| lia]
             | intros Hk; lia
             | intros Hrem;
               apply Nat.leb_le in Hle;
               simpl in Hrem;
               assert (Hinner : rem - fib (S (S k')) < fib (S k')) by
                 (rewrite fib_step in Hrem; lia);
               assert (Hrem'' : rem'' < fib (S k')) by (apply Hbd; exact Hinner);
               apply Nat.lt_le_trans with (m:=fib (S k')); [exact Hrem''|];
               simpl; apply fib_monotone_le; lia ].
        -- specialize (IH rem false xs rem' H) as [Hsum [Hz [Hall [Hlow Hbd]]]].
           refine (conj Hsum (conj Hz (conj _ (conj _ _))));
             [ simpl; apply all_le_weaken with (m:=S k'); [exact Hall| lia]
             | intros Hk; lia
             | intros Hrem;
               apply Nat.leb_gt in Hle;
               assert (Hinner : rem < fib (S (S k'))) by lia;
               assert (Hrem' : rem' < fib (S (S k'))) by (apply Hbd; exact Hinner);
               apply Nat.lt_le_trans with (m:=fib (S (S k'))); [exact Hrem'|];
               simpl; apply fib_monotone_le; lia ].
Qed.

Lemma zeck_greedy_down_inv_k0 :
  forall rem prev,
    greedy_inv 0 rem prev
      (fst (zeck_greedy_down 0 rem prev))
      (snd (zeck_greedy_down 0 rem prev)).
Proof.
  intros rem prev.
  apply zeck_greedy_down_correct_core.
  reflexivity.
Qed.

Lemma zeck_greedy_down_inv_k1 :
  forall rem prev,
    greedy_inv 1 rem prev
      (fst (zeck_greedy_down 1 rem prev))
      (snd (zeck_greedy_down 1 rem prev)).
Proof.
  intros rem prev.
  apply zeck_greedy_down_correct_core.
  reflexivity.
Qed.

Lemma zeck_greedy_down_inv_skip_prev :
  forall k rem xs rem',
    zeck_greedy_down (S (S k)) rem true = (xs, rem') ->
    greedy_inv (S (S k)) rem true xs rem'.
Proof.
  intros k rem xs rem' H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

Lemma zeck_greedy_down_inv_skip_lt :
  forall k rem xs rem',
    fib (S (S k)) > rem ->
    zeck_greedy_down (S (S k)) rem false = (xs, rem') ->
    greedy_inv (S (S k)) rem false xs rem'.
Proof.
  intros k rem xs rem' _ H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

Lemma zeck_greedy_down_inv_take :
  forall k rem xs rem',
    fib (S (S k)) <= rem ->
    zeck_greedy_down (S (S k)) rem false = (xs, rem') ->
    greedy_inv (S (S k)) rem false xs rem'.
Proof.
  intros k rem xs rem' _ H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

(*
│
│          `zeck_greedy_down_correct` is the public wrapper around the
│          core recursion lemma. It exposes the invariant without
│          committing downstream proofs to the internal case split on
│          `k` and `prev`.
│
*)

Theorem zeck_greedy_down_correct :
  forall k rem prev xs rem',
    zeck_greedy_down k rem prev = (xs, rem') ->
    greedy_inv k rem prev xs rem'.
Proof.
  intros k rem prev xs rem' H.
  destruct k as [|k'].
  - apply zeck_greedy_down_correct_core. exact H.
  - destruct k' as [|k''].
    + apply zeck_greedy_down_correct_core. exact H.
    + destruct prev.
      * apply zeck_greedy_down_inv_skip_prev. exact H.
      * destruct (Nat.leb (fib (S (S k''))) rem) eqn:Hleb.
        -- apply zeck_greedy_down_inv_take.
           ++ apply Nat.leb_le. exact Hleb.
           ++ exact H.
        -- apply zeck_greedy_down_inv_skip_lt.
           ++ apply Nat.leb_gt. exact Hleb.
           ++ exact H.
Qed.

(*
│
│          Specializing the greedy invariant at the cutoff `r0(n)`
│          shows that the residual remainder already lies below the
│          next admissible Fibonacci threshold.
│
*)

Lemma greedy_top_bound :
  forall n xs rem',
    zeck_greedy_down (r0 n) n false = (xs, rem') ->
    rem' < fib (S (r0 n)).
Proof.
  intros n xs rem' H.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' H)
    as [_ [_ [_ [_ Hbd]]]].
  simpl in Hbd.
  apply Hbd.
  apply r0_upper_S.
Qed.

(*
│
│          Whenever the greedy support begins with index `S(S(k))`,
│          the realized Fibonacci sum of that prefix remains strictly
│          below the next Fibonacci value.
│
*)

Lemma sum_fib_prefix_lt_next :
  forall k rem xs rem',
    greedy_inv (S (S k)) rem false (S (S k) :: xs) rem' ->
    rem < fib (S (S (S k))) ->
    sum_fib (S (S k) :: xs) < fib (S (S (S k))).
Proof.
  intros k rem xs rem' Hinv Hrem.
  destruct Hinv as [Hsum [_ [_ [_ _]]]].
  assert (sum_fib (S (S k) :: xs) <= rem) by lia.
  lia.
Qed.

Lemma rem_lt_1_is_0 : forall r, r < 1 -> r = 0.
Proof.
  intros r Hr. lia.
Qed.

Lemma bound_k1_le_1 : forall prev, bound 1 prev <= 1.
Proof.
  intro prev. destruct prev; simpl; lia.
Qed.

Lemma fib_2_eq_1 : fib 2 = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma fib_1_eq_1 : fib 1 = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma rem_lt_1_from_inv_k1 :
  forall rem prev xs rem',
    zeck_greedy_down 1 rem prev = (xs, rem') ->
    greedy_inv 1 rem prev xs rem' ->
    rem < fib (S (bound 1 prev)) ->
    rem' < 1.
Proof.
  intros rem prev xs rem' Hcall Hinv Hpre.
  destruct Hinv as [_ [_ [_ [_ Hbd]]]].
  specialize (Hbd Hpre).
  destruct prev.
  - simpl in Hbd. rewrite fib_1_eq_1 in Hbd. lia.
  - simpl in Hbd. rewrite fib_2_eq_1 in Hbd. lia.
Qed.

Lemma greedy_rem_lt_1_false :
  forall k rem xs rem',
    rem < fib (S k) ->
    zeck_greedy_down k rem false = (xs, rem') ->
    rem' < 1.
Proof.
  refine (well_founded_induction
            lt_wf
            (fun k =>
               forall rem xs rem',
                 rem < fib (S k) ->
                 zeck_greedy_down k rem false = (xs, rem') ->
                 rem' < 1) _).
  intros k IH rem xs rem' Hbound Hcall.
  destruct k as [|k1].
  - simpl in Hcall. inversion Hcall; subst. exact Hbound.
  - destruct k1 as [|k2].
    + simpl in Hcall. inversion Hcall; subst.
      rewrite fib_2_eq_1 in Hbound. exact Hbound.
    + simpl in Hcall.
      destruct (Nat.leb (fib (S (S k2))) rem) eqn:Hle.
      * destruct (zeck_greedy_down (S k2) (rem - fib (S (S k2))) true)
          as [xs1 rem1] eqn:Hrec.
        change
          ((S (S k2)
            :: fst (zeck_greedy_down (S k2) (rem - fib (S (S k2))) true),
            snd (zeck_greedy_down (S k2) (rem - fib (S (S k2))) true))
           = (xs, rem')) in Hcall.
        rewrite Hrec in Hcall.
        inversion Hcall; subst xs rem'. clear Hcall.
        apply Nat.leb_le in Hle.
        assert (Hrem1 : rem - fib (S (S k2)) < fib (S k2)).
        -- rewrite fib_step in Hbound. lia.
        -- destruct k2 as [|k3].
           ++ simpl in Hrec. inversion Hrec; subst.
              rewrite fib_1_eq_1 in Hrem1. exact Hrem1.
           ++ simpl in Hrec.
              pose proof (IH (S k3) ltac:(lia)) as IHk.
              exact (IHk (rem - fib (S (S (S k3)))) xs1 rem1 Hrem1 Hrec).
      * apply Nat.leb_gt in Hle.
        pose proof (IH (S k2) ltac:(lia)) as IHk.
        exact (IHk rem xs rem' Hle Hcall).
Qed.

Lemma Z0_rem_lt_1 :
  forall n xs rem',
    zeck_greedy_down (r0 n) n false = (xs, rem') ->
    rem' < 1.
Proof.
  intros n xs rem' H.
  eapply greedy_rem_lt_1_false; eauto.
  apply r0_upper_S.
Qed.

(*
│
│          `Z0_sound` is the basic adequacy theorem for the concrete
│          support extractor: reading the greedy support back through
│          `sum_fib` returns exactly the original number.
│
*)

(*                          ∀ n, sum_fib(Z0(n)) = n.                          *)

Theorem Z0_sound : forall n, sum_fib (Z0 n) = n.
Proof.
  intro n.
  unfold Z0.
  destruct (zeck_greedy_down (r0 n) n false) as [xs rem'] eqn:Hgd.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' Hgd)
    as [Hsum _].
  assert (Hrem1 : rem' < 1) by (eapply Z0_rem_lt_1; exact Hgd).
  assert (Hrem0 : rem' = 0) by (apply rem_lt_1_is_0; exact Hrem1).
  rewrite Hrem0 in Hsum.
  rewrite Nat.add_0_r in Hsum.
  exact Hsum.
Qed.

(*
│
│          `Z0_valid` complements `Z0_sound`: the extractor produces a
│          canonical admissible support, not merely a summing support.
│
*)

(*                          ∀ n, zeck_valid(Z0(n)).                           *)

Theorem Z0_valid : forall n, zeck_valid (Z0 n).
Proof.
  intro n.
  unfold Z0.
  destruct (zeck_greedy_down (r0 n) n false) as [xs rem'] eqn:Hgd.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' Hgd)
    as [_ [Hvalid _]].
  exact Hvalid.
Qed.

Lemma sum_fib_ge_head :
  forall k xs, sum_fib (k :: xs) >= fib k.
Proof.
  intros k xs. simpl. lia.
Qed.

Lemma zeck_valid_tail :
  forall k xs,
    zeck_valid (k :: xs) ->
    zeck_valid xs.
Proof.
  intros k xs [Hdec [Hadj Hge]].
  destruct xs as [|a xs'].
  - simpl. split; [trivial|]. split; trivial.
  - simpl in Hdec, Hadj, Hge.
    destruct Hdec as [_ Hdec'].
    destruct Hadj as [_ Hadj'].
    destruct Hge as [_ Hge'].
    split; [exact Hdec'|]. split; assumption.
Qed.

Lemma zeck_valid_head_ge_2 :
  forall k xs,
    zeck_valid (k :: xs) ->
    2 <= k.
Proof.
  intros k xs [_ [_ Hge]].
  simpl in Hge.
  tauto.
Qed.

Lemma fib_le_of_le : forall a b, a <= b -> fib a <= fib b.
Proof.
  intros a b Hle.
  destruct (Nat.eq_dec a b) as [Heq|Hneq].
  - subst. apply Nat.le_refl.
  - apply fib_monotone_le. lia.
Qed.

Lemma fib_lt_succ_of_ge2 : forall k, 2 <= k -> fib k < fib (S k).
Proof.
  intros k Hk.
  destruct k as [|[|k']]; try lia.
  replace (fib (S (S (S k')))) with (fib (S (S k')) + fib (S k')) by
      (symmetry; apply fib_step).
  assert (Hpos : fib (S k') >= 1) by apply fib_pos_S.
  lia.
Qed.

Lemma fib_step_pred : forall k, 1 <= k -> fib (S k) = fib k + fib (Nat.pred k).
Proof.
  intros k Hk.
  destruct k as [|k']; [lia|].
  destruct k' as [|k''].
  - vm_compute. reflexivity.
  - simpl. apply fib_step.
Qed.

Lemma sum_fib_lt_next_of_valid :
  forall k xs,
    zeck_valid (k :: xs) ->
    sum_fib (k :: xs) < fib (S k).
Proof.
  intros k xs Hvalid.
  revert k Hvalid.
  induction xs as [|x xs' IH]; intros k Hvalid; simpl.
  - apply zeck_valid_head_ge_2 in Hvalid.
    rewrite Nat.add_0_r.
    apply fib_lt_succ_of_ge2.
    exact Hvalid.
  - pose proof (zeck_valid_tail k (x :: xs') Hvalid) as Htail_valid.
    pose proof (IH x Htail_valid) as Htail.
    destruct Hvalid as [_ [Hadj _]].
    simpl in Hadj.
    destruct Hadj as [Hgap _].
    assert (Hsx : S x <= Nat.pred k) by lia.
    assert (Hsx_le : fib (S x) <= fib (Nat.pred k)).
    + apply fib_le_of_le. exact Hsx.
    + assert (Hk1 : 1 <= k) by lia.
      assert (Hstep : fib (S k) = fib k + fib (Nat.pred k)).
      * apply fib_step_pred. exact Hk1.
      * rewrite Hstep.
        assert (Hlt_pred : fib x + sum_fib xs' < fib (Nat.pred k)).
        -- eapply Nat.lt_le_trans; [exact Htail | exact Hsx_le].
        -- lia.
Qed.

Lemma sum_fib_cons_pos_valid :
  forall k xs,
    zeck_valid (k :: xs) ->
    0 < sum_fib (k :: xs).
Proof.
  intros k xs Hvalid.
  simpl.
  assert (Hk2 : 2 <= k) by (apply zeck_valid_head_ge_2 with (xs:=xs); exact Hvalid).
  assert (Hf : fib k >= 1) by (apply fib_pos; lia).
  lia.
Qed.

Lemma fib_succ_le_of_lt_ge2 :
  forall a b,
    2 <= a ->
    a < b ->
    fib (S a) <= fib b.
Proof.
  intros a b Ha Hlt.
  destruct (Nat.eq_dec (S a) b) as [Heq|Hneq].
  - subst. apply Nat.le_refl.
  - apply fib_monotone_le. lia.
Qed.

(*
│
│          `Zeckendorf_unique_core` is the canonicality theorem for
│          valid supports: equal Fibonacci sums force equality of the
│          supports themselves.
│
*)

(*        zeck_valid(xs) ∧ zeck_valid(ys) ∧ sum_fib(xs) = sum_fib(ys)         *)
(*                                 ⇒ xs = ys.                                 *)

Lemma Zeckendorf_unique_core :
  forall xs ys,
    zeck_valid xs ->
    zeck_valid ys ->
    sum_fib xs = sum_fib ys ->
    xs = ys.
Proof.
  induction xs as [|k xs IH]; intros ys Hx Hy Heq.
  - destruct ys as [|l ys].
    + reflexivity.
    + exfalso.
      pose proof (sum_fib_cons_pos_valid l ys Hy) as Hpos.
      rewrite <- Heq in Hpos. simpl in Hpos. lia.
  - destruct ys as [|l ys].
    + exfalso.
      pose proof (sum_fib_cons_pos_valid k xs Hx) as Hpos.
      rewrite Heq in Hpos. simpl in Hpos. lia.
    + assert (Hk : k = l).
      * destruct (Nat.lt_ge_cases k l) as [Hkl|Hkge].
        -- pose proof (sum_fib_lt_next_of_valid k xs Hx) as Hup.
           pose proof (sum_fib_ge_head l ys) as Hlow.
           rewrite Heq in Hup.
           assert (Hf : fib (S k) <= fib l).
           ++ apply fib_succ_le_of_lt_ge2.
              ** apply zeck_valid_head_ge_2 with (xs:=xs). exact Hx.
              ** exact Hkl.
           ++ lia.
        -- destruct (Nat.lt_ge_cases l k) as [Hlk|Hlge].
           ++ pose proof (sum_fib_lt_next_of_valid l ys Hy) as Hup.
              pose proof (sum_fib_ge_head k xs) as Hlow.
              rewrite <- Heq in Hup.
              assert (Hf : fib (S l) <= fib k).
              ** apply fib_succ_le_of_lt_ge2.
                 --- apply zeck_valid_head_ge_2 with (xs:=ys). exact Hy.
                 --- exact Hlk.
              ** lia.
           ++ lia.
      * subst l.
        apply f_equal.
        apply IH.
        -- apply zeck_valid_tail with (k:=k). exact Hx.
        -- apply zeck_valid_tail with (k:=k). exact Hy.
        -- simpl in Heq. lia.
Qed.

(*
│
│          `Z0_of_sum_fib` is the converse of `Z0_sound`: every valid
│          support is fixed by the extractor.
│
*)

(*                   zeck_valid(xs) ⇒ Z0(sum_fib(xs)) = xs.                   *)

Theorem Z0_of_sum_fib :
  forall xs, zeck_valid xs -> Z0 (sum_fib xs) = xs.
Proof.
  intros xs Hvalid.
  apply Zeckendorf_unique_core.
  - apply Z0_valid.
  - exact Hvalid.
  - apply Z0_sound.
Qed.

(*
│
│          We may therefore treat admissible Fibonacci supports as
│          canonical objects: among valid supports, equality of the
│          evaluated sums forces equality of the supports themselves.
│
*)

Theorem Zeckendorf_unique :
  forall xs ys,
    zeck_valid xs ->
    zeck_valid ys ->
    sum_fib xs = sum_fib ys ->
    xs = ys.
Proof.
  intros xs ys Hx Hy Heq.
  rewrite <- (Z0_of_sum_fib xs Hx).
  rewrite <- (Z0_of_sum_fib ys Hy).
  f_equal.
  exact Heq.
Qed.

Lemma sum_fib_app : forall xs ys, sum_fib (xs ++ ys) = sum_fib xs + sum_fib ys.
Proof.
  induction xs as [|a xs IH]; intro ys; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma all_ge_2_in :
  forall xs k, all_ge_2 xs -> In k xs -> 2 <= k.
Proof.
  induction xs as [|a xs IH]; intros k Hge Hin; simpl in *.
  - contradiction.
  - destruct Hge as [Ha Hxs].
    destruct Hin as [<-|Hin].
    + exact Ha.
    + apply (IH k Hxs Hin).
Qed.

Lemma all_le_in :
  forall m xs k, all_le m xs -> In k xs -> k <= m.
Proof.
  induction xs as [|a xs IH]; intros k Hle Hin; simpl in *.
  - contradiction.
  - destruct Hle as [Ha Hxs].
    destruct Hin as [<-|Hin].
    + exact Ha.
    + apply (IH k Hxs Hin).
Qed.

Lemma sum_fib_in_ge :
  forall xs k, In k xs -> fib k <= sum_fib xs.
Proof.
  induction xs as [|a xs IH]; intros k Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + lia.
    + specialize (IH k Hin). lia.
Qed.

(*
│
│          Every index produced by the concrete extractor lies
│          strictly below the cutoff `r0(x)`, so the recovered support
│          never reaches the boundary-defining index itself.
│
*)

Lemma Z0_indices_below_r0 :
  forall x e,
    In e (Z0 x) ->
    e < r0 x.
Proof.
  intros x e Hin.
  unfold Z0 in Hin.
  destruct (zeck_greedy_down (r0 x) x false) as [xs rem'] eqn:Hgd.
  simpl in Hin.
  pose proof (zeck_greedy_down_correct (r0 x) x false xs rem' Hgd)
    as [Hsum [_ [Hall _]]].
  assert (Hele : e <= r0 x).
  - apply (all_le_in (r0 x) xs e Hall Hin).
  - destruct (Nat.eq_dec e (r0 x)) as [Heq|Hneq].
    + subst e.
      assert (Hf_le : fib (r0 x) <= sum_fib xs).
      * apply sum_fib_in_ge. exact Hin.
      * assert (Hf_le_x : fib (r0 x) <= x) by lia.
        pose proof (r0_upper x) as Hru.
        lia.
    + lia.
Qed.

Lemma two_S : forall n, two (S n) = S (S (two n)).
Proof.
  intro n.
  unfold two.
  simpl.
  rewrite Nat.add_succ_r.
  reflexivity.
Qed.

Lemma is_even_two : forall n, is_even (two n) = true.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite two_S. simpl. exact IH.
Qed.

Lemma is_even_S_two_false : forall n, is_even (S (two n)) = false.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite two_S. simpl. exact IH.
Qed.

Lemma two_j_minus1_formula :
  forall j, two_j_minus1 j = 2 * j - 1.
Proof.
  intro j.
  unfold two_j_minus1.
  rewrite <- Nat.sub_1_r.
  unfold two.
  lia.
Qed.

Lemma two_j_minus1_lt :
  forall a b, b < a -> two_j_minus1 b < two_j_minus1 a.
Proof.
  intros a b Hlt.
  repeat rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma two_j_minus1_gap2 :
  forall a b, a >= b + 2 -> two_j_minus1 a >= two_j_minus1 b + 2.
Proof.
  intros a b Hgap.
  repeat rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma two_j_minus1_ge_1 :
  forall j, 1 <= j -> 1 <= two_j_minus1 j.
Proof.
  intros j Hj.
  rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma is_even_two_plus :
  forall a n, is_even (two a + n) = is_even n.
Proof.
  induction a as [|a IH]; intro n.
  - simpl. reflexivity.
  - rewrite two_S. simpl. apply IH.
Qed.

Lemma is_even_double_plus :
  forall a n, is_even (2 * a + n) = is_even n.
Proof.
  induction a as [|a IH]; intro n.
  - simpl. reflexivity.
  - replace (2 * S a + n) with (S (S (2 * a + n))) by lia.
    simpl.
    apply IH.
Qed.

Lemma is_even_two_j_minus1_false :
  forall j, 1 <= j -> is_even (two_j_minus1 j) = false.
Proof.
  intros j Hj.
  destruct j as [|j']; [lia|].
  unfold two_j_minus1.
  rewrite two_S.
  apply is_even_S_two_false.
Qed.

Lemma strictly_decreasing_map_two :
  forall xs, strictly_decreasing xs -> strictly_decreasing (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hdec; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma no_adjacent_map_two :
  forall xs, no_adjacent xs -> no_adjacent (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hadj; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma all_ge_2_map_two :
  forall xs, all_ge_2 xs -> all_ge_2 (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hge; simpl; auto.
  destruct Hge as [Ha Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma strictly_decreasing_map_odd :
  forall Bx xs,
    strictly_decreasing xs ->
    strictly_decreasing (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hdec.
  revert Bx Hdec.
  induction xs as [|a xs IH]; intros Bx Hdec; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  split.
  - apply Nat.add_lt_mono_l. apply two_j_minus1_lt. exact Hab.
  - apply IH. exact Htail.
Qed.

Lemma no_adjacent_map_odd :
  forall Bx xs,
    no_adjacent xs ->
    no_adjacent (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hadj.
  revert Bx Hadj.
  induction xs as [|a xs IH]; intros Bx Hadj; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  split.
  - assert (Hgap : two_j_minus1 a >= two_j_minus1 b + 2).
    + apply two_j_minus1_gap2. exact Hab.
    + lia.
  - apply IH. exact Htail.
Qed.

Lemma all_ge_2_map_odd :
  forall Bx xs,
    all_ge_2 xs ->
    all_ge_2 (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hge.
  revert Bx Hge.
  induction xs as [|a xs IH]; intros Bx Hge; simpl; auto.
  destruct Hge as [Ha Htail].
  split.
  - rewrite two_j_minus1_formula.
    lia.
  - apply IH. exact Htail.
Qed.

(*
│
│          The next block transports Zeckendorf admissibility through
│          the even and odd embedding maps that define the pairing
│          support.
│
*)

Lemma even_band_valid :
  forall x, zeck_valid (even_band base_params x).
Proof.
  intro x.
  unfold even_band, base_params.
  pose proof (Z0_valid x) as [Hdec [Hadj Hge]].
  split.
  - apply strictly_decreasing_map_two. exact Hdec.
  - split.
    + apply no_adjacent_map_two. exact Hadj.
    + apply all_ge_2_map_two. exact Hge.
Qed.

Lemma odd_band_valid :
  forall x y, zeck_valid (odd_band base_params x y).
Proof.
  intros x y.
  unfold odd_band, base_params.
  pose proof (Z0_valid y) as [Hdec [Hadj Hge]].
  split.
  - apply strictly_decreasing_map_odd. exact Hdec.
  - split.
    + apply no_adjacent_map_odd. exact Hadj.
    + apply all_ge_2_map_odd. exact Hge.
Qed.

(*                        e ∈ even_band(x) ⇒ e < B(x).                        *)

Lemma even_band_lt_B :
  forall x e, In e (even_band base_params x) -> e < B base_params x.
Proof.
  intros x e Hin.
  unfold even_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [He Hj]].
  subst e.
  assert (Hjlt : j < r0 x).
  - apply Z0_indices_below_r0. exact Hj.
  - unfold base_params.
    unfold B.
    unfold two.
    simpl.
    replace (2 * r0 x) with (r0 x + r0 x) by lia.
    lia.
Qed.

(*                     o ∈ odd_band(x, y) ⇒ B(x) + 1 ≤ o.                     *)

Lemma odd_band_ge_B1 :
  forall x y o, In o (odd_band base_params x y) -> S (B base_params x) <= o.
Proof.
  intros x y o Hin.
  unfold odd_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Ho Hj]].
  subst o.
  assert (Hj2 : 2 <= j).
  - apply all_ge_2_in with (xs:=Z0 y); [|exact Hj].
    destruct (Z0_valid y) as [_ [_ Hge]]; exact Hge.
  - assert (Hj1 : 1 <= j) by lia.
    assert (Hodd1 : 1 <= two_j_minus1 j) by (apply two_j_minus1_ge_1; exact Hj1).
    unfold B.
    unfold base_params.
    simpl.
    lia.
Qed.

(*
│
│          The odd band sits strictly above the even band: every
│          odd-band index dominates every even-band index associated
│          with the same left coordinate.
│
*)

Lemma odd_band_gt_even_band :
  forall x y o e,
    In o (odd_band base_params x y) ->
    In e (even_band base_params x) ->
    o > e.
Proof.
  intros x y o e Ho He.
  pose proof (odd_band_ge_B1 x y o Ho) as Hob.
  pose proof (even_band_lt_B x e He) as Heb.
  lia.
Qed.

Lemma odd_band_gap_even_band :
  forall x y o e,
    In o (odd_band base_params x y) ->
    In e (even_band base_params x) ->
    o >= e + 2.
Proof.
  intros x y o e Ho He.
  pose proof (odd_band_ge_B1 x y o Ho) as Hob.
  pose proof (even_band_lt_B x e He) as Heb.
  lia.
Qed.

Lemma all_ge_2_app :
  forall xs ys, all_ge_2 xs -> all_ge_2 ys -> all_ge_2 (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy; simpl.
  - exact Hy.
  - destruct Hx as [Ha Hxs]. split; [exact Ha|]. apply IH; assumption.
Qed.

Lemma strictly_decreasing_app :
  forall xs ys,
    strictly_decreasing xs ->
    strictly_decreasing ys ->
    (forall x y, In x xs -> In y ys -> x > y) ->
    strictly_decreasing (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy Hcross; simpl.
  - exact Hy.
  - destruct xs as [|b xs'].
    + simpl.
      destruct ys as [|y ys'].
      * simpl. exact I.
      * simpl. split.
        -- apply Hcross; simpl; auto.
        -- exact Hy.
    + simpl in Hx.
      destruct Hx as [Hab Htail].
      simpl.
      split; [exact Hab|].
      apply IH; try assumption.
      intros x y Hinx Hiny.
      apply Hcross; simpl; auto.
Qed.

Lemma no_adjacent_app :
  forall xs ys,
    no_adjacent xs ->
    no_adjacent ys ->
    (forall x y, In x xs -> In y ys -> x >= y + 2) ->
    no_adjacent (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy Hcross; simpl.
  - exact Hy.
  - destruct xs as [|b xs'].
    + simpl.
      destruct ys as [|y ys'].
      * simpl. exact I.
      * simpl. split.
        -- apply Hcross; simpl; auto.
        -- exact Hy.
    + simpl in Hx.
      destruct Hx as [Hab Htail].
      simpl.
      split; [exact Hab|].
      apply IH; try assumption.
      intros x y Hinx Hiny.
      apply Hcross; simpl; auto.
Qed.

(*
│
│          `odd_even_concat_valid` is the structural compatibility
│          lemma for pairing. The two bands remain sufficiently
│          separated that their concatenation is again a valid
│          Zeckendorf support.
│
*)

Lemma odd_even_concat_valid :
  forall x y,
    zeck_valid (odd_band base_params x y ++ even_band base_params x).
Proof.
  intros x y.
  pose proof (odd_band_valid x y) as [Hdec_o [Hadj_o Hge_o]].
  pose proof (even_band_valid x) as [Hdec_e [Hadj_e Hge_e]].
  split.
  - eapply strictly_decreasing_app; eauto.
    intros o e Ho He.
    apply odd_band_gt_even_band with (x:=x) (y:=y); assumption.
  - split.
    + eapply no_adjacent_app; eauto.
      intros o e Ho He.
      apply odd_band_gap_even_band with (x:=x) (y:=y); assumption.
    + apply all_ge_2_app; assumption.
Qed.

Lemma pair_base_as_odd_even_sum :
  forall x y,
    pair base_params x y =
    sum_fib (odd_band base_params x y ++ even_band base_params x).
Proof.
  intros x y.
  unfold pair.
  rewrite !sum_fib_app.
  lia.
Qed.

(*
│
│          The “carryless” code therefore admits a canonical odd/even
│          support decomposition.
│
*)

(*              Z0(pair(x, y)) = odd_band(x, y) ⧺ even_band(x).               *)

Theorem Z0_pair_is_concat :
  forall x y,
    Z0 (pair base_params x y) =
    odd_band base_params x y ++ even_band base_params x.
Proof.
  intros x y.
  rewrite pair_base_as_odd_even_sum.
  apply Z0_of_sum_fib.
  apply odd_even_concat_valid.
Qed.

Lemma even_band_even :
  forall x k,
    In k (even_band base_params x) ->
    is_even k = true.
Proof.
  intros x k Hin.
  unfold even_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [e [He _]].
  subst k.
  apply is_even_two.
Qed.

Lemma odd_band_even_false :
  forall x y k,
    In k (odd_band base_params x y) ->
    is_even k = false.
Proof.
  intros x y k Hin.
  unfold odd_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Hk Hj]].
  subst k.
  assert (Hj2 : 2 <= j).
  - apply all_ge_2_in with (xs:=Z0 y); [|exact Hj].
    destruct (Z0_valid y) as [_ [_ Hge]]; exact Hge.
  - assert (Hj1 : 1 <= j) by lia.
    unfold B.
    rewrite is_even_double_plus.
    apply is_even_two_j_minus1_false.
    exact Hj1.
Qed.

Lemma odd_band_odd_ge_B1_true :
  forall x y k,
    In k (odd_band base_params x y) ->
    odd_ge_B1 (B base_params x) k = true.
Proof.
  intros x y k Hin.
  unfold odd_ge_B1.
  unfold is_odd.
  rewrite (odd_band_even_false x y k Hin).
  apply Nat.leb_le.
  apply (odd_band_ge_B1 x y k).
  exact Hin.
Qed.

Lemma even_band_odd_ge_B1_false :
  forall x k,
    In k (even_band base_params x) ->
    odd_ge_B1 (B base_params x) k = false.
Proof.
  intros x k Hin.
  unfold odd_ge_B1.
  unfold is_odd.
  rewrite (even_band_even x k Hin).
  reflexivity.
Qed.

Lemma filter_false_nil :
  forall (A : Type) (p : A -> bool) (xs : list A),
    (forall a, In a xs -> p a = false) ->
    filter p xs = [].
Proof.
  intros A p xs Hp.
  induction xs as [|a xs IH]; simpl.
  - reflexivity.
  - assert (Ha : p a = false) by (apply Hp; simpl; auto).
    rewrite Ha.
    apply IH.
    intros b Hb.
    apply Hp.
    simpl; auto.
Qed.

Lemma filter_true_id :
  forall (A : Type) (p : A -> bool) (xs : list A),
    (forall a, In a xs -> p a = true) ->
    filter p xs = xs.
Proof.
  intros A p xs Hp.
  induction xs as [|a xs IH]; simpl.
  - reflexivity.
  - assert (Ha : p a = true) by (apply Hp; simpl; auto).
    rewrite Ha.
    simpl.
    f_equal.
    apply IH.
    intros b Hb.
    apply Hp.
    simpl; auto.
Qed.

(*
│
│          The final filtering corollaries recover the two pairing
│          bands directly from the canonical support of a paired code.
│
*)

(*            ∀ x y, {e ∈ Z0(pair(x, y)) ∣ 2 ∣ e} = even_band(x).             *)

Corollary Z0_even_split :
  forall x y,
    filter is_even (Z0 (pair base_params x y)) = even_band base_params x.
Proof.
  intros x y.
  rewrite Z0_pair_is_concat.
  rewrite filter_app.
  assert (Hodd_nil : filter is_even (odd_band base_params x y) = []).
  - apply filter_false_nil. intros a Ha. apply (odd_band_even_false x y a); exact Ha.
  - assert (Heven_id :
      filter is_even (even_band base_params x) = even_band base_params x).
    + apply filter_true_id. intros a Ha. apply (even_band_even x a); exact Ha.
    + rewrite Hodd_nil, Heven_id. reflexivity.
Qed.

(*             ∀ x y, {k ∈ Z0(pair(x, y)) ∣ 2 ∤ k ∧ B(x) + 1 ≤ k}             *)
(*                             = odd_band(x, y).                              *)

Corollary Z0_odd_split :
  forall x y,
    filter (odd_ge_B1 (B base_params x))
      (Z0 (pair base_params x y)) =
    odd_band base_params x y.
Proof.
  intros x y.
  rewrite Z0_pair_is_concat.
  rewrite filter_app.
  assert (Hodd_id :
    filter (odd_ge_B1 (B base_params x))
      (odd_band base_params x y) =
    odd_band base_params x y).
  - apply filter_true_id. intros a Ha. apply (odd_band_odd_ge_B1_true x y a); exact Ha.
  - assert (Heven_nil :
      filter (odd_ge_B1 (B base_params x)) (even_band base_params x) = []).
    + apply filter_false_nil. intros a Ha. apply (even_band_odd_ge_B1_false x a); exact Ha.
    + rewrite Hodd_id, Heven_nil.
      rewrite app_nil_r.
      reflexivity.
Qed.
