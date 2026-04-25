(*P002_10__Binomial_TwoAdic_Core.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / P002_10__Binomial_TwoAdic_Core                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file is the arithmetic core for the packed carryless-to-Diophantine
  bridge. It contains only ordinary central-binomial, finite-bitcount,
  divisibility, two-adic, and factorial-route vocabulary.

  It deliberately does not import the packed-mask or local-semantics layers.
  Later files use this core to state the Kummer/Legendre endpoint and then
  connect that endpoint to the concrete stacked carryless instance.

*)

(*
│
│          This arithmetic core uses binary naturals, linear
│          arithmetic, and the standard natural-number library for
│          Pascal recursion.
│
*)

(*                               ℕ₂ ∧ lia ∧ nat                               *)

From Stdlib Require Import NArith Lia PeanoNat.

Local Open Scope N_scope.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                         CENTRAL BINOMIAL SURFACE                        ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The binomial coefficient is introduced by Pascal recursion
│          over `nat`.
│
*)

(*            Binom(n,0)=1; Binom(S n,S k)=Binom(n,k)+Binom(n,S k)            *)

Fixpoint binomial_nat (n k : nat) : nat :=
  match n, k with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S n', S k' => (binomial_nat n' k' + binomial_nat n' (S k'))%nat
  end.

(*
│
│          The public central-binomial value remains the
│          Pascal-recursive coefficient `C(2r,r)`.
│
*)

(*                           Central(r)=Binom(2r,r)                           *)

Definition central_binomial (r : N) : N :=
  N.of_nat (binomial_nat (N.to_nat (2 * r)) (N.to_nat r)).

(*
│
│          Divisibility over binary naturals is represented by an
│          explicit multiplier witness.
│
*)

(*                              d∣n ⇔ ∃ q. n=d·q                              *)

Definition dividesN (d n : N) : Prop :=
  exists q, n = d * q.

(*
│
│          Every power of two is strictly positive.
│
*)

(*                                    0<2ᵏ                                    *)

Lemma pow2_value_positive :
  forall k,
    0 < 2 ^ k.
Proof.
  induction k using N.peano_ind.
  - reflexivity.
  - rewrite N.pow_succ_r by lia.
    nia.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                             FINITE BITCOUNTS                            ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          A Boolean bit contributes one when true and zero when
│          false.
│
*)

(*                         bit(true)=1 ∧ bit(false)=0                         *)

Definition bit_value (b : bool) : N :=
  if b then 1 else 0.

(*
│
│          A finite bitcount window sums the tested bits in positions
│          below the window size.
│
*)

(*                   BitcountWindow(n,x)=Σᵢ₍₀≤i<n₎ bit(xᵢ)                    *)

Fixpoint bitcount_window (n : nat) (x : N) : N :=
  match n with
  | O => 0
  | S n' => bitcount_window n' x + bit_value (N.testbit x (N.of_nat n'))
  end.

(*
│
│          The full bitcount counts the finite window determined by
│          `N.size`.
│
*)

(*                      Pop(x)=BitcountWindow(size(x),x)                      *)

Definition full_bitcount (x : N) : N :=
  bitcount_window (N.to_nat (N.size x)) x.

(*
│
│          A single Boolean bit contributes at most one.
│
*)

(*                                  bit(b)≤1                                  *)

Lemma bit_value_bound :
  forall b,
    bit_value b <= 1.
Proof.
  destruct b; unfold bit_value; lia.
Qed.

(*
│
│          A bitcount over an `n`-slot window is bounded by `n`.
│
*)

(*                           BitcountWindow(n,x)≤n                            *)

Lemma bitcount_window_bound :
  forall n x,
    bitcount_window n x <= N.of_nat n.
Proof.
  induction n as [|n IH]; intro x; simpl.
  - lia.
  - pose proof (IH x).
    destruct (N.testbit x (N.of_nat n)); unfold bit_value; lia.
Qed.

(*
│
│          Two values with equal bits throughout a window have equal
│          bitcounts in that window.
│
*)

(*     ∀ i<n. bit(x,i)=bit(y,i) ⇒ BitcountWindow(n,x)=BitcountWindow(n,y)     *)

Lemma bitcount_window_ext :
  forall n x y,
    (forall i,
      i < N.of_nat n ->
      N.testbit x i = N.testbit y i) ->
    bitcount_window n x = bitcount_window n y.
Proof.
  induction n as [|n IH]; intros x y Hbits; cbn [bitcount_window].
  - reflexivity.
  - rewrite IH with (y := y).
    + rewrite Hbits by (rewrite Nat2N.inj_succ; lia).
      reflexivity.
    + intros i Hi.
      apply Hbits.
      rewrite Nat2N.inj_succ.
      lia.
Qed.

(*
│
│          Bits at or above `N.size x` are false.
│
*)

(*                           size(x)≤i ⇒ bit(x,i)=0                           *)

Lemma testbit_above_size_false :
  forall x i,
    N.size x <= i ->
    N.testbit x i = false.
Proof.
  intros x i Hsize.
  destruct (N.eq_0_gt_0_cases x) as [->|Hxpos].
  - apply N.bits_0.
  - rewrite N.size_log2 in Hsize by lia.
    apply N.bits_above_log2.
    lia.
Qed.

(*
│
│          A value below `2^k` has binary size at most `k`.
│
*)

(*                              x<2ᵏ ⇒ size(x)≤k                              *)

Lemma size_le_pow2_bound :
  forall k x,
    x < 2 ^ k ->
    N.size x <= k.
Proof.
  intros k x Hx.
  destruct (N.eq_0_gt_0_cases x) as [->|Hxpos].
  - simpl.
    lia.
  - rewrite N.size_log2 by lia.
    apply (proj1 (N.log2_lt_pow2 x k Hxpos)) in Hx.
    lia.
Qed.

(*
│
│          Extending a bitcount window through a region whose bits are
│          all false does not change the count.
│
*)

(*   n≤m ∧ ∀ i∈[n,m). bit(x,i)=0 ⇒ BitcountWindow(m,x)=BitcountWindow(n,x)    *)

Lemma bitcount_window_extend_high_false :
  forall m n x,
    (n <= m)%nat ->
    (forall i,
      N.of_nat n <= i < N.of_nat m ->
      N.testbit x i = false) ->
    bitcount_window m x = bitcount_window n x.
Proof.
  induction m as [|m IH]; intros n x Hle Hbits.
  - assert (n = 0)%nat by lia.
    subst n.
    reflexivity.
  - destruct (Nat.eq_dec n (S m)) as [->|Hne].
    + reflexivity.
    + assert (Hle' : (n <= m)%nat) by lia.
      simpl.
      rewrite Hbits.
      * unfold bit_value.
        rewrite N.add_0_r.
        apply IH.
        -- exact Hle'.
        -- intros i Hi.
           apply Hbits.
           rewrite Nat2N.inj_succ.
           lia.
      * rewrite Nat2N.inj_succ.
        lia.
Qed.

(*
│
│          If `x` is below `2^k`, the `k`-window bitcount is already
│          the full bitcount.
│
*)

(*                     x<2ᵏ ⇒ BitcountWindow(k,x)=Pop(x)                      *)

Lemma bitcount_window_full_under_pow2_bound :
  forall k x,
    x < 2 ^ k ->
    bitcount_window (N.to_nat k) x = full_bitcount x.
Proof.
  intros k x Hx.
  unfold full_bitcount.
  apply bitcount_window_extend_high_false.
  - pose proof (size_le_pow2_bound k x Hx).
    lia.
  - intros i [Hlo _Hhi].
    apply testbit_above_size_false.
    rewrite N2Nat.id in Hlo.
    exact Hlo.
Qed.

(*
│
│          The one-step divide-by-two identity separates the low bit
│          from the remaining shifted window.
│
*)

(*           BitcountWindow(S n,x)=bit(x₀)+BitcountWindow(n,⌊x÷2⌋)            *)

Lemma bitcount_window_succ_div2 :
  forall n x,
    bitcount_window (S n) x =
    bit_value (N.testbit x 0) + bitcount_window n (x / 2).
Proof.
  induction n as [|n IH]; intro x; cbn [bitcount_window].
  - change (N.of_nat 0) with 0.
    destruct (N.testbit x 0); reflexivity.
  - change
      (bitcount_window (S n) x +
       bit_value (N.testbit x (N.of_nat (S n))) =
       bit_value (N.testbit x 0) +
       (bitcount_window n (x / 2) +
        bit_value (N.testbit (x / 2) (N.of_nat n)))).
    rewrite IH.
    rewrite N.div2_bits.
    replace (N.of_nat (S n)) with (N.succ (N.of_nat n))
      by (rewrite Nat2N.inj_succ; reflexivity).
    lia.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                    CENTRAL BINOMIAL BITCOUNT ENDPOINT                   ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The central-binomial bitcount bridge is the exact endpoint
│          later files consume: divisibility by `2^m` is equivalent to
│          `m` being below the bitcount of `R`.
│
*)

(*                          2ᵐ∣Central(R) ⇔ m≤Pop(R)                          *)

Definition central_binomial_bitcount_bridge : Prop :=
  forall R m,
    dividesN (2 ^ m) (central_binomial R) <->
    m <= full_bitcount R.

(*
│
│          The right edge of Pascal's triangle is one.
│
*)

(*                                Binom(n,0)=1                                *)

Lemma binomial_nat_0_r :
  forall n,
    binomial_nat n 0 = 1%nat.
Proof.
  destruct n; reflexivity.
Qed.

(*
│
│          The positive upper entries above row zero are zero.
│
*)

(*                               Binom(0,S k)=0                               *)

Lemma binomial_nat_0_l_succ :
  forall k,
    binomial_nat 0 (S k) = 0%nat.
Proof.
  reflexivity.
Qed.

(*
│
│          Pascal coefficients above the diagonal vanish.
│
*)

(*                             n<k ⇒ Binom(n,k)=0                             *)

Lemma binomial_nat_above_diag :
  forall n k,
    (n < k)%nat ->
    binomial_nat n k = 0%nat.
Proof.
  induction n as [|n IH]; intros k Hlt.
  - destruct k as [|k].
    + lia.
    + reflexivity.
  - destruct k as [|k].
    + lia.
    + cbn [binomial_nat].
      rewrite IH by lia.
    rewrite IH by lia.
    reflexivity.
Qed.

(*
│
│          Pascal coefficients on the diagonal are one.
│
*)

(*                                Binom(n,n)=1                                *)

Lemma binomial_nat_diag :
  forall n,
    binomial_nat n n = 1%nat.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [binomial_nat].
    rewrite IH.
    rewrite binomial_nat_above_diag by lia.
    reflexivity.
Qed.

(*
│
│          The zeroth central binomial coefficient is one.
│
*)

(*                                Central(0)=1                                *)

Lemma central_binomial_0 :
  central_binomial 0 = 1.
Proof.
  reflexivity.
Qed.

(*
│
│          Every divisor divides zero.
│
*)

(*                                    d∣0                                     *)

Lemma dividesN_0_r :
  forall d,
    dividesN d 0.
Proof.
  intro d.
  exists 0.
  rewrite N.mul_0_r.
  reflexivity.
Qed.

(*
│
│          Divisibility is reflexive.
│
*)

(*                                    n∣n                                     *)

Lemma dividesN_refl :
  forall n,
    dividesN n n.
Proof.
  intro n.
  exists 1.
  rewrite N.mul_1_r.
  reflexivity.
Qed.

(*
│
│          One divides every binary natural.
│
*)

(*                                    1∣n                                     *)

Lemma dividesN_1_l :
  forall n,
    dividesN 1 n.
Proof.
  intro n.
  exists n.
  rewrite N.mul_1_l.
  reflexivity.
Qed.

(*
│
│          A divisor of `n` also divides any right multiple of `n`.
│
*)

(*                                d∣n ⇒ d∣n·k                                 *)

Lemma dividesN_mul_r :
  forall d n k,
    dividesN d n ->
    dividesN d (n * k).
Proof.
  intros d n k [q Hq].
  exists (q * k).
  subst n.
  rewrite N.mul_assoc.
  reflexivity.
Qed.

(*
│
│          A divisor of `n` also divides any left multiple of `n`.
│
*)

(*                                d∣n ⇒ d∣k·n                                 *)

Lemma dividesN_mul_l :
  forall d n k,
    dividesN d n ->
    dividesN d (k * n).
Proof.
  intros d n k Hdiv.
  rewrite N.mul_comm.
  apply dividesN_mul_r.
  exact Hdiv.
Qed.

(*
│
│          Divisibility is transitive.
│
*)

(*                              a∣b ∧ b∣c ⇒ a∣c                               *)

Lemma dividesN_trans :
  forall a b c,
    dividesN a b ->
    dividesN b c ->
    dividesN a c.
Proof.
  intros a b c [q Hb] [r Hc].
  exists (q * r).
  subst b c.
  rewrite N.mul_assoc.
  reflexivity.
Qed.

(*
│
│          Exact division on the right reconstructs the original
│          value.
│
*)

(*                           d≠0 ∧ d∣n ⇒ (n÷d)·d=n                            *)

Lemma dividesN_div_exact_r :
  forall d n,
    d <> 0 ->
    dividesN d n ->
    n / d * d = n.
Proof.
  intros d n Hd [q Hq].
  subst n.
  replace (d * q / d) with q.
  - rewrite N.mul_comm.
    reflexivity.
  - rewrite N.mul_comm.
    symmetry.
    apply N.div_mul.
    exact Hd.
Qed.

(*
│
│          Exact division on the left reconstructs the original value.
│
*)

(*                           d≠0 ∧ d∣n ⇒ d·(n÷d)=n                            *)

Lemma dividesN_div_exact_l :
  forall d n,
    d <> 0 ->
    dividesN d n ->
    d * (n / d) = n.
Proof.
  intros d n Hd Hdiv.
  rewrite N.mul_comm.
  apply dividesN_div_exact_r; assumption.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        TWO-ADIC DIVISIBILITY SEAM                       ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The lower-bound two-adic predicate is just divisibility by
│          `2^m`.
│
*)

(*                            OrderGe(n,m) ⇔ 2ᵐ∣n                             *)

Definition two_adic_order_ge (n m : N) : Prop :=
  dividesN (2 ^ m) n.

(*
│
│          Every value has at least zero factors of two.
│
*)

(*                                OrderGe(n,0)                                *)

Lemma two_adic_order_ge_zero_exponent :
  forall n,
    two_adic_order_ge n 0.
Proof.
  intro n.
  unfold two_adic_order_ge.
  simpl.
  apply dividesN_1_l.
Qed.

(*
│
│          Zero is divisible by every power of two.
│
*)

(*                                OrderGe(0,m)                                *)

Lemma two_adic_order_ge_zero_value :
  forall m,
    two_adic_order_ge 0 m.
Proof.
  intro m.
  unfold two_adic_order_ge.
  apply dividesN_0_r.
Qed.

(*
│
│          A stronger two-adic lower bound implies every weaker lower
│          bound.
│
*)

(*                   lo≤hi ∧ OrderGe(n,hi) ⇒ OrderGe(n,lo)                    *)

Lemma two_adic_order_ge_weaken :
  forall n lo hi,
    lo <= hi ->
    two_adic_order_ge n hi ->
    two_adic_order_ge n lo.
Proof.
  intros n lo hi Hle [q Hq].
  unfold two_adic_order_ge.
  exists (2 ^ (hi - lo) * q).
  subst n.
  rewrite N.mul_assoc.
  rewrite <- N.pow_add_r.
  replace (lo + (hi - lo)) with hi by lia.
  reflexivity.
Qed.

(*
│
│          Two-adic lower bounds add under multiplication.
│
*)

(*               OrderGe(n,a) ∧ OrderGe(m,b) ⇒ OrderGe(n·m,a+b)               *)

Lemma two_adic_order_ge_mul :
  forall n m a b,
    two_adic_order_ge n a ->
    two_adic_order_ge m b ->
    two_adic_order_ge (n * m) (a + b).
Proof.
  intros n m a b [q Hn] [r Hm].
  unfold two_adic_order_ge.
  exists (q * r).
  subst n m.
  rewrite N.pow_add_r.
  nia.
Qed.

(*
│
│          If `2^k` is divisible by `2^m`, then `m≤k`.
│
*)

(*                            OrderGe(2ᵏ,m) ⇒ m≤k                             *)

Lemma two_adic_order_ge_pow_forward :
  forall k m,
    two_adic_order_ge (2 ^ k) m ->
    m <= k.
Proof.
  intros k m [q Hq].
  destruct (N.le_gt_cases m k) as [Hle|Hgt].
  - exact Hle.
  - destruct (N.eq_dec q 0) as [Hq0|Hqnonzero].
    + subst q.
      rewrite N.mul_0_r in Hq.
      pose proof (pow2_value_positive k).
      lia.
    + assert (Hqpos : 0 < q).
      {
        apply (proj1 (N.neq_0_lt_0 q)).
        exact Hqnonzero.
      }
      assert (Hlt : 2 ^ k < 2 ^ m).
      {
        apply N.pow_lt_mono_r; lia.
      }
      assert (Hmul : 2 ^ m <= 2 ^ m * q).
      {
        pose proof (pow2_value_positive m).
        nia.
      }
      nia.
Qed.

(*
│
│          If `m≤k`, then `2^k` is divisible by `2^m`.
│
*)

(*                            m≤k ⇒ OrderGe(2ᵏ,m)                             *)

Lemma two_adic_order_ge_pow_backward :
  forall k m,
    m <= k ->
    two_adic_order_ge (2 ^ k) m.
Proof.
  intros k m Hle.
  unfold two_adic_order_ge.
  exists (2 ^ (k - m)).
  rewrite <- N.pow_add_r.
  replace (m + (k - m)) with k by lia.
  reflexivity.
Qed.

(*
│
│          The exact lower-bound profile of a pure power of two is its
│          exponent.
│
*)

(*                            OrderGe(2ᵏ,m) ⇔ m≤k                             *)

Lemma two_adic_order_ge_pow_exact :
  forall k m,
    two_adic_order_ge (2 ^ k) m <-> m <= k.
Proof.
  intros k m.
  split.
  - apply two_adic_order_ge_pow_forward.
  - apply two_adic_order_ge_pow_backward.
Qed.

(*
│
│          Exact two-adic order is represented extensionally: the
│          lower-bound predicate holds exactly up to exponent `e`.
│
*)

(*                    Exact(n,e) ⇔ ∀ m. OrderGe(n,m) ⇔ m≤e                    *)

Definition two_adic_exact (n e : N) : Prop :=
  forall m,
    two_adic_order_ge n m <-> m <= e.

(*
│
│          A pure power of two has exact two-adic order equal to its
│          exponent.
│
*)

(*                                Exact(2ᵏ,k)                                 *)

Lemma two_adic_exact_pow2 :
  forall k,
    two_adic_exact (2 ^ k) k.
Proof.
  unfold two_adic_exact.
  intros k m.
  apply two_adic_order_ge_pow_exact.
Qed.

(*
│
│          One has exact two-adic order zero.
│
*)

(*                                 Exact(1,0)                                 *)

Lemma two_adic_exact_one :
  two_adic_exact 1 0.
Proof.
  change 1 with (2 ^ 0).
  apply two_adic_exact_pow2.
Qed.

(*
│
│          An odd value is not divisible by two.
│
*)

(*                           Odd(n) ⇒ ¬OrderGe(n,1)                           *)

Lemma odd_not_divisible_by_two :
  forall n,
    N.odd n = true ->
    ~ two_adic_order_ge n 1.
Proof.
  intros n Hodd [q Hq].
  rewrite Hq in Hodd.
  change (2 ^ 1) with 2 in Hodd.
  rewrite N.odd_mul in Hodd.
  discriminate.
Qed.

(*
│
│          An odd value has exact two-adic order zero.
│
*)

(*                            Odd(n) ⇒ Exact(n,0)                             *)

Lemma two_adic_exact_odd :
  forall n,
    N.odd n = true ->
    two_adic_exact n 0.
Proof.
  unfold two_adic_exact.
  intros n Hodd m.
  split.
  - intro Hge.
    destruct (N.eq_dec m 0) as [->|Hmnonzero].
    + lia.
    + exfalso.
      apply (odd_not_divisible_by_two n Hodd).
      apply (two_adic_order_ge_weaken n 1 m).
      * lia.
      * exact Hge.
  - intro Hle.
    assert (m = 0) by lia.
    subst m.
    apply two_adic_order_ge_zero_exponent.
Qed.

(*
│
│          Divisibility by one more factor of two across `2·n` is
│          equivalent to divisibility of `n`.
│
*)

(*                       OrderGe(2n,S m) ⇔ OrderGe(n,m)                       *)

Lemma two_adic_order_ge_double_succ :
  forall n m,
    two_adic_order_ge (2 * n) (N.succ m) <->
    two_adic_order_ge n m.
Proof.
  intros n m.
  split.
  - intros [q Hq].
    unfold two_adic_order_ge.
    exists q.
    rewrite N.pow_succ_r in Hq by lia.
    replace (2 ^ m * 2 * q) with (2 * (2 ^ m * q)) in Hq by nia.
    replace (2 * 2 ^ m * q) with (2 * (2 ^ m * q)) in Hq by nia.
    rewrite <- !N.double_spec in Hq.
    apply N.double_inj in Hq.
    exact Hq.
  - intros [q Hq].
    unfold two_adic_order_ge.
    exists q.
    subst n.
    rewrite N.pow_succ_r by lia.
    nia.
Qed.

(*
│
│          Multiplication by an odd factor on the right does not
│          create extra two-adic lower-bound content.
│
*)

(*                   Odd(o) ∧ OrderGe(n·o,m) ⇒ OrderGe(n,m)                   *)

Lemma two_adic_order_ge_mul_odd_cancel_r :
  forall n o m,
    N.odd o = true ->
    two_adic_order_ge (n * o) m ->
    two_adic_order_ge n m.
Proof.
  intros n o m Hodd.
  revert n.
  induction m using N.peano_ind.
  - intros n Hge.
    apply two_adic_order_ge_zero_exponent.
  - intros n Hge.
    destruct Hge as [q Hq].
    destruct (N.Even_or_Odd n) as [[n' Hn]|Hnodd].
    + subst n.
      apply two_adic_order_ge_double_succ.
      apply IHm.
      unfold two_adic_order_ge.
      exists q.
      rewrite N.pow_succ_r in Hq by lia.
      replace ((2 * n') * o) with (2 * (n' * o)) in Hq by nia.
      replace (2 ^ m * 2 * q) with (2 * (2 ^ m * q)) in Hq by nia.
      replace (2 * 2 ^ m * q) with (2 * (2 ^ m * q)) in Hq by nia.
      rewrite <- !N.double_spec in Hq.
      apply N.double_inj in Hq.
      exact Hq.
    + exfalso.
      assert (Hnodd_bool : N.odd n = true).
      {
        apply N.odd_spec.
        exact Hnodd.
      }
      assert (Hprod_odd : N.odd (n * o) = true).
      {
        rewrite N.odd_mul.
        rewrite Hnodd_bool, Hodd.
        reflexivity.
      }
      rewrite Hq in Hprod_odd.
      rewrite N.pow_succ_r in Hprod_odd by lia.
      replace (2 ^ m * 2 * q) with (2 * (2 ^ m * q)) in Hprod_odd by nia.
      replace (2 * 2 ^ m * q) with (2 * (2 ^ m * q)) in Hprod_odd by nia.
      rewrite N.odd_even in Hprod_odd.
      discriminate.
Qed.

(*
│
│          Multiplication by an odd factor on the left does not create
│          extra two-adic lower-bound content.
│
*)

(*                   Odd(o) ∧ OrderGe(o·n,m) ⇒ OrderGe(n,m)                   *)

Lemma two_adic_order_ge_mul_odd_cancel_l :
  forall o n m,
    N.odd o = true ->
    two_adic_order_ge (o * n) m ->
    two_adic_order_ge n m.
Proof.
  intros o n m Hodd Hge.
  rewrite N.mul_comm in Hge.
  apply (two_adic_order_ge_mul_odd_cancel_r n o m); assumption.
Qed.

(*
│
│          Multiplication by an odd factor on the right preserves
│          exact two-adic order.
│
*)

(*                     Odd(o) ∧ Exact(n,e) ⇒ Exact(n·o,e)                     *)

Lemma two_adic_exact_mul_odd_r :
  forall n o e,
    N.odd o = true ->
    two_adic_exact n e ->
    two_adic_exact (n * o) e.
Proof.
  unfold two_adic_exact.
  intros n o e Hodd Hexact m.
  split.
  - intro Hge.
    apply Hexact.
    apply (two_adic_order_ge_mul_odd_cancel_r n o m); assumption.
  - intro Hle.
    replace m with (m + 0) by lia.
    apply two_adic_order_ge_mul.
    + apply Hexact.
      exact Hle.
    + apply two_adic_order_ge_zero_exponent.
Qed.

(*
│
│          Multiplication by an odd factor on the left preserves exact
│          two-adic order.
│
*)

(*                     Odd(o) ∧ Exact(n,e) ⇒ Exact(o·n,e)                     *)

Lemma two_adic_exact_mul_odd_l :
  forall o n e,
    N.odd o = true ->
    two_adic_exact n e ->
    two_adic_exact (o * n) e.
Proof.
  intros o n e Hodd Hexact.
  rewrite N.mul_comm.
  apply two_adic_exact_mul_odd_r; assumption.
Qed.

(*
│
│          Doubling a value increments its exact two-adic order.
│
*)

(*                         Exact(n,e) ⇒ Exact(2n,S e)                         *)

Lemma two_adic_exact_double :
  forall n e,
    two_adic_exact n e ->
    two_adic_exact (2 * n) (N.succ e).
Proof.
  unfold two_adic_exact.
  intros n e Hexact m.
  induction m using N.peano_ind.
  - split.
    + intro Hge.
      lia.
    + intro Hle.
      apply two_adic_order_ge_zero_exponent.
  - rewrite two_adic_order_ge_double_succ.
    rewrite Hexact.
    lia.
Qed.

(*
│
│          Two has exact two-adic order one.
│
*)

(*                                 Exact(2,1)                                 *)

Lemma two_adic_exact_two :
  two_adic_exact 2 1.
Proof.
  change 2 with (2 ^ 1).
  apply two_adic_exact_pow2.
Qed.

(*
│
│          Doubling shifts the finite bitcount window upward and
│          leaves the count unchanged after dropping the low zero bit.
│
*)

(*                 BitcountWindow(S n,2x)=BitcountWindow(n,x)                 *)

Lemma bitcount_window_double_succ :
  forall n x,
    bitcount_window (S n) (2 * x) = bitcount_window n x.
Proof.
  intros n x.
  rewrite bitcount_window_succ_div2.
  rewrite N.testbit_even_0.
  unfold bit_value.
  replace ((2 * x) / 2) with x.
  - reflexivity.
  - symmetry.
    rewrite N.mul_comm.
    apply N.div_mul.
    lia.
Qed.

(*
│
│          Full bitcount is invariant under doubling.
│
*)

(*                               Pop(2x)=Pop(x)                               *)

Lemma full_bitcount_double :
  forall x,
    full_bitcount (2 * x) = full_bitcount x.
Proof.
  intro x.
  destruct (N.eq_dec x 0) as [->|Hxnonzero].
  - reflexivity.
  - unfold full_bitcount.
    rewrite (N.size_log2 (2 * x)).
    rewrite (N.size_log2 x) by exact Hxnonzero.
    + rewrite N.log2_double.
      * repeat rewrite N2Nat.inj_succ.
        rewrite bitcount_window_double_succ.
        reflexivity.
      * apply (proj1 (N.neq_0_lt_0 x)).
        exact Hxnonzero.
    + intro Hzero.
      apply Hxnonzero.
      nia.
Qed.

(*
│
│          Every binary power dominates the successor of its exponent.
│
*)

(*                                   S k≤2ᵏ                                   *)

Lemma succ_le_pow2_self :
  forall k,
    N.succ k <= 2 ^ k.
Proof.
  induction k using N.peano_ind.
  - reflexivity.
  - rewrite N.pow_succ_r by lia.
    nia.
Qed.

(*
│
│          The binary size of a value is bounded by the value itself.
│
*)

(*                                 size(x)≤x                                  *)

Lemma size_le_self :
  forall x,
    N.size x <= x.
Proof.
  intro x.
  destruct (N.eq_dec x 0) as [->|Hxnonzero].
  - reflexivity.
  - rewrite N.size_log2 by exact Hxnonzero.
    pose proof (N.log2_spec x ltac:(lia)) as [Hlow _].
    pose proof (succ_le_pow2_self (N.log2 x)).
    lia.
Qed.

(*
│
│          The full bitcount of a value is bounded by the value
│          itself.
│
*)

(*                                  Pop(x)≤x                                  *)

Lemma full_bitcount_le_self :
  forall x,
    full_bitcount x <= x.
Proof.
  intro x.
  unfold full_bitcount.
  pose proof (bitcount_window_bound (N.to_nat (N.size x)) x) as Hbits.
  rewrite N2Nat.id in Hbits.
  pose proof (size_le_self x).
  lia.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                 FACTORIAL ROUTE FOR THE CENTRAL BINOMIAL                ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The nat-indexed factorial returns a binary natural value.
│
*)

(*                 FactNat(0)=1 ∧ FactNat(S n)=S n·FactNat(n)                 *)

Fixpoint factorial_natN (n : nat) : N :=
  match n with
  | O => 1
  | S n' => N.of_nat (S n') * factorial_natN n'
  end.

(*
│
│          The binary-natural factorial delegates to the nat-indexed
│          factorial after `N.to_nat`.
│
*)

(*                         Fact(n)=FactNat(toNat(n))                          *)

Definition factorialN (n : N) : N :=
  factorial_natN (N.to_nat n).

(*
│
│          The factorial-form binomial value is the quotient
│          `n!/(k!(n−k)!)`.
│
*)

(*                 BinomFact(n,k)=Fact(n)÷(Fact(k)·Fact(n−k))                 *)

Definition binomial_factorial_value (n k : N) : N :=
  factorialN n / (factorialN k * factorialN (n - k)).

(*
│
│          The factorial-form binomial denominator is `k!(n−k)!`.
│
*)

(*                        Denom(n,k)=Fact(k)·Fact(n−k)                        *)

Definition binomial_factorial_denominator (n k : N) : N :=
  factorialN k * factorialN (n - k).

(*
│
│          The central factorial-form binomial specializes the
│          factorial quotient to `(2r,r)`.
│
*)

(*                       CentralFact(r)=BinomFact(2r,r)                       *)

Definition central_binomial_factorial_value (r : N) : N :=
  binomial_factorial_value (2 * r) r.

(*
│
│          The binomial factorial bridge contract says the Pascal and
│          factorial formulas agree below the diagonal.
│
*)

(*                      k≤n ⇒ Binom(n,k)=BinomFact(n,k)                       *)

Definition binomial_factorial_bridge : Prop :=
  forall n k,
    k <= n ->
    N.of_nat (binomial_nat (N.to_nat n) (N.to_nat k)) =
    binomial_factorial_value n k.

(*
│
│          The central factorial bridge contract says the public
│          central binomial agrees with the factorial surface.
│
*)

(*                         Central(r)=CentralFact(r)                          *)

Definition central_binomial_factorial_bridge : Prop :=
  forall r,
    central_binomial r = central_binomial_factorial_value r.

(*
│
│          The central factorial two-adic bridge contract is the
│          bitcount endpoint stated on the factorial surface.
│
*)

(*                    OrderGe(CentralFact(r),m) ⇔ m≤Pop(r)                    *)

Definition central_binomial_factorial_two_adic_bridge : Prop :=
  forall r m,
    two_adic_order_ge (central_binomial_factorial_value r) m <->
    m <= full_bitcount r.

(*
│
│          The denominator-divisibility contract says `k!(n−k)!`
│          divides `n!` whenever `k≤n`.
│
*)

(*                          k≤n ⇒ Denom(n,k)∣Fact(n)                          *)

Definition binomial_factorial_denominator_divides : Prop :=
  forall n k,
    k <= n ->
    dividesN (binomial_factorial_denominator n k) (factorialN n).

(*
│
│          The factorial valuation contract is Legendre's base-two
│          formula, stated as exact two-adic order. This file names
│          the contract; it is proved downstream.
│
*)

(*                          Exact(Fact(n),n−Pop(n))                           *)

Definition factorial_two_adic_exact : Prop :=
  forall n,
    two_adic_exact (factorialN n) (n - full_bitcount n).

(*
│
│          The exact-order multiplication contract says exact
│          exponents add under multiplication. This file only names
│          the contract.
│
*)

(*                Exact(a,eₐ) ∧ Exact(b,eᵦ) ⇒ Exact(a·b,eₐ+eᵦ)                *)

Definition two_adic_exact_mul_adds : Prop :=
  forall a b ea eb,
    two_adic_exact a ea ->
    two_adic_exact b eb ->
    two_adic_exact (a * b) (ea + eb).

(*
│
│          The exact-order quotient contract says exact exponents
│          subtract across an exact nonzero quotient. This file only
│          names the contract.
│
*)

(*      q·d=n ∧ d≠0 ∧ eᵈ≤eⁿ ∧ Exact(n,eⁿ) ∧ Exact(d,eᵈ) ⇒ Exact(q,eⁿ−eᵈ)      *)

Definition two_adic_exact_quotient_subtracts : Prop :=
  forall n d q en ed,
    q * d = n ->
    d <> 0 ->
    ed <= en ->
    two_adic_exact n en ->
    two_adic_exact d ed ->
    two_adic_exact q (en - ed).

(*
│
│          The nat-indexed factorial unfolds at successors.
│
*)

(*                        FactNat(S n)=S n·FactNat(n)                         *)

Lemma factorial_natN_succ :
  forall n,
    factorial_natN (S n) = N.of_nat (S n) * factorial_natN n.
Proof.
  reflexivity.
Qed.

(*
│
│          A positive factorial difference also unfolds at the
│          successor boundary.
│
*)

(*                  k<n ⇒ FactNat(n−k)=(n−k)·FactNat(n−S k)                   *)

Lemma factorial_natN_sub_succ :
  forall n k,
    (k < n)%nat ->
    factorial_natN (n - k) =
    N.of_nat (n - k) * factorial_natN (n - S k).
Proof.
  intros n k Hlt.
  replace (n - k)%nat with (S (n - S k)) by lia.
  reflexivity.
Qed.

(*
│
│          A successor plus the complementary subtraction reconstructs
│          the successor of the total.
│
*)

(*                            k≤n ⇒ S k+(n−k)=S n                             *)

Lemma nat_succ_plus_sub :
  forall n k,
    (k <= n)%nat ->
    (S k + (n - k) = S n)%nat.
Proof.
  intros n k Hle.
  lia.
Qed.

(*
│
│          Zero factorial is one.
│
*)

(*                                 Fact(0)=1                                  *)

Lemma factorialN_0 :
  factorialN 0 = 1.
Proof.
  reflexivity.
Qed.

(*
│
│          The binary-natural factorial unfolds at successors.
│
*)

(*                           Fact(S n)=S n·Fact(n)                            *)

Lemma factorialN_succ :
  forall n,
    factorialN (N.succ n) = N.succ n * factorialN n.
Proof.
  intro n.
  unfold factorialN.
  rewrite N2Nat.inj_succ.
  cbn [factorial_natN].
  rewrite Nat2N.inj_succ.
  rewrite N2Nat.id.
  reflexivity.
Qed.

(*
│
│          The nat-indexed factorial is strictly positive.
│
*)

(*                                0<FactNat(n)                                *)

Lemma factorial_natN_positive :
  forall n,
    0 < factorial_natN n.
Proof.
  induction n as [|n IH].
  - simpl.
    lia.
  - cbn [factorial_natN].
    assert (0 < N.of_nat (S n)) by lia.
    nia.
Qed.

(*
│
│          The binary-natural factorial is strictly positive.
│
*)

(*                                 0<Fact(n)                                  *)

Lemma factorialN_positive :
  forall n,
    0 < factorialN n.
Proof.
  intro n.
  unfold factorialN.
  apply factorial_natN_positive.
Qed.

(*
│
│          The binary-natural factorial is nonzero.
│
*)

(*                                 Fact(n)≠0                                  *)

Lemma factorialN_nonzero :
  forall n,
    factorialN n <> 0.
Proof.
  intro n.
  pose proof (factorialN_positive n).
  lia.
Qed.

(*
│
│          The core factorial identity clears denominators for Pascal
│          binomial coefficients below the diagonal.
│
*)

(*           k≤n ⇒ Binom(n,k)·(FactNat(k)·FactNat(n−k))=FactNat(n)            *)

Lemma binomial_nat_factorial_identity :
  forall n k,
    (k <= n)%nat ->
    N.of_nat (binomial_nat n k) *
    (factorial_natN k * factorial_natN (n - k)) =
    factorial_natN n.
Proof.
  induction n as [|n IH]; intros k Hle.
  - assert (k = 0)%nat by lia.
    subst k.
    reflexivity.
  - destruct k as [|k].
    + cbn [binomial_nat factorial_natN].
      replace (S n - 0)%nat with (S n) by lia.
      rewrite N.mul_1_l.
      rewrite N.mul_1_l.
      reflexivity.
    + cbn [binomial_nat factorial_natN].
      rewrite Nat2N.inj_add.
      destruct (Nat.eq_dec k n) as [->|Hkne].
      * rewrite binomial_nat_diag.
        rewrite binomial_nat_above_diag by lia.
        replace (S n - S n)%nat with 0%nat by lia.
        cbn [factorial_natN].
        nia.
      * assert (Hklt : (k < n)%nat) by lia.
        assert (HSkle : (S k <= n)%nat) by lia.
        pose proof (IH k ltac:(lia)) as Hleft.
        pose proof (IH (S k) HSkle) as Hright.
        rewrite factorial_natN_succ in Hright.
        rewrite factorial_natN_sub_succ in Hleft by exact Hklt.
        replace (S n - S k)%nat with (n - k)%nat by lia.
        rewrite factorial_natN_sub_succ by exact Hklt.
        assert (Hsum : N.of_nat (S k + (n - k)) = N.of_nat (S n)).
        {
          f_equal.
          apply nat_succ_plus_sub.
          lia.
        }
        rewrite Nat2N.inj_add in Hsum.
        rewrite <- Hsum.
        set (a := N.of_nat (binomial_nat n k)) in *.
        set (b := N.of_nat (binomial_nat n (S k))) in *.
        set (sk := N.of_nat (S k)) in *.
        set (nk := N.of_nat (n - k)) in *.
        set (f := factorial_natN k) in *.
        set (h := factorial_natN (n - S k)) in *.
        set (fn := factorial_natN n) in *.
        replace ((a + b) * ((sk * f) * (nk * h)))
          with (sk * (a * (f * (nk * h))) + nk * (b * ((sk * f) * h)))
          by nia.
        rewrite Hleft, Hright.
        nia.
Qed.

(*
│
│          The nat-indexed denominator divides the nat-indexed
│          factorial below the diagonal.
│
*)

(*                  k≤n ⇒ FactNat(k)·FactNat(n−k)∣FactNat(n)                  *)

Lemma binomial_factorial_denominator_divides_nat :
  forall n k,
    (k <= n)%nat ->
    dividesN
      (factorial_natN k * factorial_natN (n - k))
      (factorial_natN n).
Proof.
  intros n k Hle.
  exists (N.of_nat (binomial_nat n k)).
  rewrite N.mul_comm.
  symmetry.
  apply binomial_nat_factorial_identity.
  exact Hle.
Qed.

(*
│
│          The binary-natural denominator-divisibility contract is
│          proved from the nat-indexed factorial identity.
│
*)

(*                          k≤n ⇒ Denom(n,k)∣Fact(n)                          *)

Theorem binomial_factorial_denominator_divides_proved :
  binomial_factorial_denominator_divides.
Proof.
  unfold binomial_factorial_denominator_divides.
  intros n k Hle.
  unfold binomial_factorial_denominator, factorialN.
  rewrite N2Nat.inj_sub.
  apply binomial_factorial_denominator_divides_nat.
  lia.
Qed.

(*
│
│          A factorial divides its successor factorial.
│
*)

(*                             Fact(n)∣Fact(S n)                              *)

Lemma factorialN_divides_succ :
  forall n,
    dividesN (factorialN n) (factorialN (N.succ n)).
Proof.
  intro n.
  rewrite factorialN_succ.
  rewrite N.mul_comm.
  apply dividesN_mul_r.
  apply dividesN_refl.
Qed.

(*
│
│          A factorial divides every later factorial obtained by
│          adding an offset.
│
*)

(*                             Fact(a)∣Fact(a+d)                              *)

Lemma factorialN_divides_add :
  forall a d,
    dividesN (factorialN a) (factorialN (a + d)).
Proof.
  intros a d.
  induction d using N.peano_ind.
  - rewrite N.add_0_r.
    apply dividesN_refl.
  - rewrite N.add_succ_r.
    eapply dividesN_trans.
    + exact IHd.
    + apply factorialN_divides_succ.
Qed.

(*
│
│          A factorial divides any factorial at a greater or equal
│          index.
│
*)

(*                           a≤b ⇒ Fact(a)∣Fact(b)                            *)

Lemma factorialN_divides_le :
  forall a b,
    a <= b ->
    dividesN (factorialN a) (factorialN b).
Proof.
  intros a b Hle.
  replace b with (a + (b - a)) by lia.
  apply factorialN_divides_add.
Qed.

(*
│
│          The quotient of a successor factorial by the previous
│          factorial is the successor index.
│
*)

(*                           Fact(S n)÷Fact(n)=S n                            *)

Lemma factorialN_succ_div_self :
  forall n,
    factorialN (N.succ n) / factorialN n = N.succ n.
Proof.
  intro n.
  rewrite factorialN_succ.
  apply N.div_mul.
  apply factorialN_nonzero.
Qed.

(*
│
│          The central factorial value at zero is one.
│
*)

(*                              CentralFact(0)=1                              *)

Lemma central_binomial_factorial_value_0 :
  central_binomial_factorial_value 0 = 1.
Proof.
  reflexivity.
Qed.

(*
│
│          The factorial-form binomial value at `k=0` is one.
│
*)

(*                              BinomFact(n,0)=1                              *)

Lemma binomial_factorial_value_n_0 :
  forall n,
    binomial_factorial_value n 0 = 1.
Proof.
  intro n.
  unfold binomial_factorial_value.
  rewrite factorialN_0.
  replace (1 * factorialN (n - 0)) with (factorialN n) by (rewrite N.sub_0_r; lia).
  apply N.div_same.
  apply factorialN_nonzero.
Qed.

(*
│
│          The factorial-form binomial value on the diagonal is one.
│
*)

(*                              BinomFact(n,n)=1                              *)

Lemma binomial_factorial_value_n_n :
  forall n,
    binomial_factorial_value n n = 1.
Proof.
  intro n.
  unfold binomial_factorial_value.
  replace (n - n) with 0 by lia.
  rewrite factorialN_0.
  replace (factorialN n * 1) with (factorialN n) by lia.
  apply N.div_same.
  apply factorialN_nonzero.
Qed.

(*
│
│          The factorial-form binomial value at `(0,0)` is one.
│
*)

(*                              BinomFact(0,0)=1                              *)

Lemma binomial_factorial_value_0_0 :
  binomial_factorial_value 0 0 = 1.
Proof.
  apply binomial_factorial_value_n_0.
Qed.

(*
│
│          The factorial-form denominator is strictly positive.
│
*)

(*                                0<Denom(n,k)                                *)

Lemma binomial_factorial_denominator_positive :
  forall n k,
    0 < binomial_factorial_denominator n k.
Proof.
  intros n k.
  unfold binomial_factorial_denominator.
  pose proof (factorialN_positive k).
  pose proof (factorialN_positive (n - k)).
  nia.
Qed.

(*
│
│          The factorial-form denominator is nonzero.
│
*)

(*                                Denom(n,k)≠0                                *)

Lemma binomial_factorial_denominator_nonzero :
  forall n k,
    binomial_factorial_denominator n k <> 0.
Proof.
  intros n k.
  pose proof (binomial_factorial_denominator_positive n k).
  lia.
Qed.

(*
│
│          When the denominator divides the numerator, the quotient
│          value multiplies back to the factorial numerator.
│
*)

(*           Denom(n,k)∣Fact(n) ⇒ BinomFact(n,k)·Denom(n,k)=Fact(n)           *)

Lemma binomial_factorial_value_exact_under_divisibility :
  forall n k,
    dividesN (binomial_factorial_denominator n k) (factorialN n) ->
    binomial_factorial_value n k *
    binomial_factorial_denominator n k = factorialN n.
Proof.
  intros n k Hdiv.
  unfold binomial_factorial_value.
  fold (binomial_factorial_denominator n k).
  apply dividesN_div_exact_r.
  - apply binomial_factorial_denominator_nonzero.
  - exact Hdiv.
Qed.

(*
│
│          The Pascal and factorial binomial surfaces agree below the
│          diagonal.
│
*)

(*                      k≤n ⇒ Binom(n,k)=BinomFact(n,k)                       *)

Theorem binomial_factorial_bridge_proved :
  binomial_factorial_bridge.
Proof.
  unfold binomial_factorial_bridge.
  intros n k Hle.
  apply N.mul_reg_r with (p := binomial_factorial_denominator n k).
  - apply binomial_factorial_denominator_nonzero.
  - symmetry.
    rewrite binomial_factorial_value_exact_under_divisibility.
    + unfold binomial_factorial_denominator, factorialN.
      rewrite N2Nat.inj_sub.
      symmetry.
      apply binomial_nat_factorial_identity.
      lia.
    + apply binomial_factorial_denominator_divides_proved.
      exact Hle.
Qed.

(*
│
│          The factorial denominator divides the numerator at both
│          binomial edges.
│
*)

(*                  Denom(n,0)∣Fact(n) ∧ Denom(n,n)∣Fact(n)                   *)

Lemma binomial_factorial_denominator_divides_edges :
  forall n,
    dividesN (binomial_factorial_denominator n 0) (factorialN n) /\
    dividesN (binomial_factorial_denominator n n) (factorialN n).
Proof.
  intro n.
  split.
  - unfold binomial_factorial_denominator.
    rewrite factorialN_0.
    replace (1 * factorialN (n - 0)) with (factorialN n)
      by (rewrite N.sub_0_r; lia).
    apply dividesN_refl.
  - unfold binomial_factorial_denominator.
    replace (n - n) with 0 by lia.
    rewrite factorialN_0.
    replace (factorialN n * 1) with (factorialN n) by lia.
    apply dividesN_refl.
Qed.

(*
│
│          The factorial bridge specializes correctly at `k=0`.
│
*)

(*                         Binom(n,0)=BinomFact(n,0)                          *)

Lemma binomial_factorial_bridge_k0 :
  forall n,
    N.of_nat (binomial_nat (N.to_nat n) 0) =
    binomial_factorial_value n 0.
Proof.
  intro n.
  rewrite binomial_nat_0_r.
  rewrite binomial_factorial_value_n_0.
  reflexivity.
Qed.

(*
│
│          The factorial bridge specializes correctly on the diagonal.
│
*)

(*                         Binom(n,n)=BinomFact(n,n)                          *)

Lemma binomial_factorial_bridge_diag :
  forall n,
    N.of_nat (binomial_nat (N.to_nat n) (N.to_nat n)) =
    binomial_factorial_value n n.
Proof.
  intro n.
  rewrite binomial_nat_diag.
  rewrite binomial_factorial_value_n_n.
  reflexivity.
Qed.

(*
│
│          The central factorial bridge follows from the full binomial
│          factorial bridge by specializing to `(2r,r)`.
│
*)

(*                 BinomialBridge ⇒ Central(r)=CentralFact(r)                 *)

Theorem central_binomial_factorial_bridge_from_binomial_factorial_bridge :
  binomial_factorial_bridge ->
  central_binomial_factorial_bridge.
Proof.
  intros Hbridge r.
  unfold central_binomial, central_binomial_factorial_value.
  apply Hbridge.
  lia.
Qed.

(*
│
│          The public central-binomial surface agrees with the
│          factorial central-binomial surface.
│
*)

(*                         Central(r)=CentralFact(r)                          *)

Theorem central_binomial_factorial_bridge_proved :
  central_binomial_factorial_bridge.
Proof.
  apply central_binomial_factorial_bridge_from_binomial_factorial_bridge.
  exact binomial_factorial_bridge_proved.
Qed.

(*
│
│          The exponent difference produced by the factorial quotient
│          simplifies to the bitcount of `r`.
│
*)

(*                 2r−Pop(2r)−((r−Pop(r))+(r−Pop(r)))=Pop(r)                  *)

Lemma central_factorial_two_adic_exponent :
  forall r,
    (2 * r - full_bitcount (2 * r)) -
    ((r - full_bitcount r) + (r - full_bitcount r)) =
    full_bitcount r.
Proof.
  intro r.
  rewrite full_bitcount_double.
  pose proof (full_bitcount_le_self r).
  nia.
Qed.

(*
│
│          The denominator exponent is bounded by the numerator
│          exponent in the central factorial quotient.
│
*)

(*                      (r−Pop(r))+(r−Pop(r))≤2r−Pop(2r)                      *)

Lemma central_factorial_denominator_exponent_le :
  forall r,
    (r - full_bitcount r) + (r - full_bitcount r) <=
    2 * r - full_bitcount (2 * r).
Proof.
  intro r.
  rewrite full_bitcount_double.
  pose proof (full_bitcount_le_self r).
  nia.
Qed.

(*
│
│          If Legendre's factorial exactness and exact-order
│          multiplication and quotient laws are supplied, then the
│          central factorial two-adic bridge follows.
│
*)

(*   Legendre ∧ ExactMul ∧ ExactQuot ⇒ OrderGe(CentralFact(r),m) ⇔ m≤Pop(r)   *)

Theorem central_binomial_factorial_two_adic_bridge_from_exact_route :
  factorial_two_adic_exact ->
  two_adic_exact_mul_adds ->
  two_adic_exact_quotient_subtracts ->
  central_binomial_factorial_two_adic_bridge.
Proof.
  intros Hfactorial Hmul Hquot.
  unfold central_binomial_factorial_two_adic_bridge.
  intros r m.
  assert
    (Hexact :
      two_adic_exact
        (central_binomial_factorial_value r)
        (full_bitcount r)).
  {
    set (den := binomial_factorial_denominator (2 * r) r).
    assert (Hden_eq : den = factorialN r * factorialN r).
    {
      unfold den, binomial_factorial_denominator.
      replace (2 * r - r) with r by lia.
      reflexivity.
    }
    assert
      (Hden_exact :
        two_adic_exact den
          ((r - full_bitcount r) + (r - full_bitcount r))).
    {
      rewrite Hden_eq.
      apply Hmul; apply Hfactorial.
    }
    assert
      (Hquot_eq :
        central_binomial_factorial_value r * den = factorialN (2 * r)).
    {
      unfold den, central_binomial_factorial_value.
      apply binomial_factorial_value_exact_under_divisibility.
      apply binomial_factorial_denominator_divides_proved.
      lia.
    }
    pose proof
      (Hquot
        (factorialN (2 * r))
        den
        (central_binomial_factorial_value r)
        (2 * r - full_bitcount (2 * r))
        ((r - full_bitcount r) + (r - full_bitcount r))
        Hquot_eq
        ltac:(unfold den; apply binomial_factorial_denominator_nonzero)
        ltac:(apply central_factorial_denominator_exponent_le)
        (Hfactorial (2 * r))
        Hden_exact)
      as Hcentral_exact.
    replace
      ((2 * r - full_bitcount (2 * r)) -
       ((r - full_bitcount r) + (r - full_bitcount r)))
      with (full_bitcount r) in Hcentral_exact
      by (symmetry; apply central_factorial_two_adic_exponent).
    exact Hcentral_exact.
  }
  exact (Hexact m).
Qed.

(*
│
│          The public central-binomial bitcount bridge follows by
│          combining the factorial-value bridge with the
│          factorial-surface two-adic bridge.
│
*)

(*     Central=CentralFact ∧ CentralFactBridge ⇒ 2ᵐ∣Central(r) ⇔ m≤Pop(r)     *)

Theorem central_binomial_bitcount_bridge_from_factorial_route :
  central_binomial_factorial_bridge ->
  central_binomial_factorial_two_adic_bridge ->
  central_binomial_bitcount_bridge.
Proof.
  intros Hfactorial HtwoAdic.
  unfold central_binomial_bitcount_bridge.
  intros r m.
  rewrite Hfactorial.
  unfold two_adic_order_ge in HtwoAdic.
  apply HtwoAdic.
Qed.

(*
│
│          The bitcount of zero is zero.
│
*)

(*                                  Pop(0)=0                                  *)

Lemma full_bitcount_0 :
  full_bitcount 0 = 0.
Proof.
  reflexivity.
Qed.

(*
│
│          The bitcount of one is one.
│
*)

(*                                  Pop(1)=1                                  *)

Lemma full_bitcount_1 :
  full_bitcount 1 = 1.
Proof.
  reflexivity.
Qed.

(*
│
│          The central factorial two-adic bridge holds at `r=0`
│          directly.
│
*)

(*                    OrderGe(CentralFact(0),m) ⇔ m≤Pop(0)                    *)

Lemma central_binomial_factorial_two_adic_bridge_at_zero :
  forall m,
    two_adic_order_ge (central_binomial_factorial_value 0) m <->
    m <= full_bitcount 0.
Proof.
  intro m.
  rewrite central_binomial_factorial_value_0.
  rewrite full_bitcount_0.
  change 1 with (2 ^ 0).
  apply two_adic_order_ge_pow_exact.
Qed.

(*
│
│          The central factorial value at one is two.
│
*)

(*                              CentralFact(1)=2                              *)

Lemma central_binomial_factorial_value_1 :
  central_binomial_factorial_value 1 = 2.
Proof.
  reflexivity.
Qed.

(*
│
│          The central factorial two-adic bridge holds at `r=1`
│          directly.
│
*)

(*                    OrderGe(CentralFact(1),m) ⇔ m≤Pop(1)                    *)

Lemma central_binomial_factorial_two_adic_bridge_at_one :
  forall m,
    two_adic_order_ge (central_binomial_factorial_value 1) m <->
    m <= full_bitcount 1.
Proof.
  intro m.
  rewrite central_binomial_factorial_value_1.
  rewrite full_bitcount_1.
  change 2 with (2 ^ 1).
  apply two_adic_order_ge_pow_exact.
Qed.

(*
│
│          The public central-binomial bitcount bridge holds at `r=0`
│          directly.
│
*)

(*                          2ᵐ∣Central(0) ⇔ m≤Pop(0)                          *)

Lemma central_binomial_bitcount_bridge_at_zero :
  forall m,
    dividesN (2 ^ m) (central_binomial 0) <->
    m <= full_bitcount 0.
Proof.
  intro m.
  rewrite central_binomial_0.
  rewrite full_bitcount_0.
  split.
  - intro Hdiv.
    apply (two_adic_order_ge_pow_forward 0 m).
    unfold two_adic_order_ge.
    exact Hdiv.
  - intro Hm.
    assert (m = 0) by lia.
    subst m.
    simpl.
    apply dividesN_1_l.
Qed.
