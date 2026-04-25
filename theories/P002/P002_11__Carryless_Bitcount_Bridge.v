(*P002_11__Carryless_Bitcount_Bridge.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                Proofcase / P002_11__Carryless_Bitcount_Bridge                │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file proves the project-local bitcount half of the carryless/binomial
  bridge. It knows about the stacked carryless source and target values only
  as bounded natural numbers `S` and `T`; it does not construct packed-mask
  compiler instances.

  The core result is `carryless_bridge_R_bitcount_threshold_proved`: for a
  power-of-two bridge base, the explicit value `R = S(B²-B)+(T+1)(B²-1)` has
  enough one-bits exactly when `S` and `T` are carryless.

*)

(*
│
│          This file uses binary naturals, linear arithmetic, and nat
│          conversion for finite bit windows.
│
*)

(*                               ℕ₂ ∧ lia ∧ nat                               *)

From Stdlib Require Import NArith Lia PeanoNat.

(*
│
│          The bridge consumes the packed carryless predicate and the
│          binomial two-adic core, but it does not import packed trace
│          semantics.
│
*)

(*                          P002₀₇ ∧ P002₁₀ → P002₁₁                          *)

From P002 Require Import P002_07__Packed_Carryless_Masks.
From P002 Require Import P002_10__Binomial_TwoAdic_Core.

Module CC := P002_07__Packed_Carryless_Masks.

Local Notation pow2 := CC.pow2.

Local Open Scope N_scope.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        CARRYLESS BINOMIAL TARGET                        ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The carryless square modulus is the square of the bridge
│          base.
│
*)

(*                               Modulus(B)=B²                                *)

Definition carryless_square_modulus (B : N) : N :=
  B * B.

(*
│
│          The bridge value `R` combines source and target masks in
│          the fixed central-binomial argument shape.
│
*)

(*                       R(B,S,T)=S·(B²−B)+(T+1)·(B²−1)                       *)

Definition carryless_bridge_R (B S T : N) : N :=
  S * (carryless_square_modulus B - B) +
  (T + 1) * (carryless_square_modulus B - 1).

(*
│
│          The carryless binomial target asks for divisibility of
│          `Central(R)` by the square modulus.
│
*)

(*                    Target(B,S,T) ⇔ B²∣Central(R(B,S,T))                    *)

Definition carryless_binomial_target (B S T : N) : Prop :=
  dividesN (carryless_square_modulus B)
    (central_binomial (carryless_bridge_R B S T)).

(*
│
│          The well-formedness condition requires a power-of-two base
│          and both operands below that base.
│
*)

(*                      WF(B,S,T) ⇔ pow₂(B) ∧ S<B ∧ T<B                       *)

Definition carryless_binomial_wf (B S T : N) : Prop :=
  pow2 B /\ S < B /\ T < B.

(*
│
│          Soundness says carrylessness implies the binomial
│          divisibility target under well-formedness.
│
*)

(*                    WF ∧ carryless₂(S,T) ⇒ Target(B,S,T)                    *)

Definition carryless_binomial_sound : Prop :=
  forall B S T,
    carryless_binomial_wf B S T ->
    carryless2 S T ->
    carryless_binomial_target B S T.

(*
│
│          Completeness says the binomial divisibility target implies
│          carrylessness under well-formedness.
│
*)

(*                    WF ∧ Target(B,S,T) ⇒ carryless₂(S,T)                    *)

Definition carryless_binomial_complete : Prop :=
  forall B S T,
    carryless_binomial_wf B S T ->
    carryless_binomial_target B S T ->
    carryless2 S T.

(*
│
│          The carryless binomial bridge packages soundness and
│          completeness. It is derived here only conditionally from
│          the central-binomial bitcount bridge plus the local
│          threshold theorem.
│
*)

(*                 CarrylessBinomialBridge ⇔ Sound ∧ Complete                 *)

Definition carryless_binomial_bridge : Prop :=
  carryless_binomial_sound /\
  carryless_binomial_complete.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        BIT WINDOW FOR THE BRIDGE                        ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          A bit overlap at index `i` means both operands have a `1`
│          bit at that index.
│
*)

(*                  Overlap(S,T,i) ⇔ bit(S,i)=1 ∧ bit(T,i)=1                  *)

Definition bit_overlap (S T i : N) : Prop :=
  N.testbit S i = true /\ N.testbit T i = true.

(*
│
│          No overlap below `k` means there is no shared `1` bit in
│          the finite window below `k`.
│
*)

(*               NoOverlapBelow(k,S,T) ⇔ ∀ i<k. ¬Overlap(S,T,i)               *)

Definition no_bit_overlap_below (k S T : N) : Prop :=
  forall i, i < k -> ~ bit_overlap S T i.

(*
│
│          A concrete overlapping bit refutes carrylessness.
│
*)

(*                     Overlap(S,T,i) ⇒ ¬carryless₂(S,T)                      *)

Lemma bit_overlap_not_carryless :
  forall S T i,
    bit_overlap S T i ->
    ~ carryless2 S T.
Proof.
  intros S T i [HS HT] Hcarry.
  unfold carryless2 in Hcarry.
  assert (Hbit : N.testbit (N.land S T) i = false).
  {
    rewrite Hcarry.
    apply N.bits_0.
  }
  rewrite N.land_spec in Hbit.
  rewrite HS, HT in Hbit.
  discriminate.
Qed.

(*
│
│          Carrylessness rules out every concrete bit overlap.
│
*)

(*                     carryless₂(S,T) ⇒ ¬Overlap(S,T,i)                      *)

Lemma carryless2_no_bit_overlap :
  forall S T i,
    carryless2 S T ->
    ~ bit_overlap S T i.
Proof.
  intros S T i Hcarry Hoverlap.
  exact (bit_overlap_not_carryless S T i Hoverlap Hcarry).
Qed.

(*
│
│          If no bit position overlaps, then the operands are
│          carryless.
│
*)

(*                   ∀ i. ¬Overlap(S,T,i) ⇒ carryless₂(S,T)                   *)

Lemma no_bit_overlap_carryless2 :
  forall S T,
    (forall i, ~ bit_overlap S T i) ->
    carryless2 S T.
Proof.
  intros S T Hnone.
  unfold carryless2.
  apply N.bits_inj_0.
  intro i.
  rewrite N.land_spec.
  destruct (N.testbit S i) eqn:HS; destruct (N.testbit T i) eqn:HT.
  - exfalso.
    exact (Hnone i (conj HS HT)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*
│
│          Carrylessness is equivalent to having no overlapping bit
│          position.
│
*)

(*                   carryless₂(S,T) ⇔ ∀ i. ¬Overlap(S,T,i)                   *)

Lemma carryless2_iff_no_bit_overlap :
  forall S T,
    carryless2 S T <-> forall i, ~ bit_overlap S T i.
Proof.
  intros S T.
  split.
  - intros Hcarry i.
    apply carryless2_no_bit_overlap.
    exact Hcarry.
  - apply no_bit_overlap_carryless2.
Qed.

(*
│
│          A failure of carrylessness produces an explicit overlapping
│          bit index.
│
*)

(*                   ¬carryless₂(S,T) ⇒ ∃ i. Overlap(S,T,i)                   *)

Lemma not_carryless2_has_bit_overlap :
  forall S T,
    ~ carryless2 S T ->
    exists i, bit_overlap S T i.
Proof.
  intros S T Hnot.
  unfold carryless2 in Hnot.
  assert (Hpos : 0 < N.land S T).
  {
    apply (proj1 (N.neq_0_lt_0 (N.land S T))).
    exact Hnot.
  }
  exists (N.log2 (N.land S T)).
  assert (Hbit : N.testbit (N.land S T) (N.log2 (N.land S T)) = true).
  {
    apply N.bit_log2.
    apply (proj2 (N.neq_0_lt_0 (N.land S T))).
    exact Hpos.
  }
  rewrite N.land_spec in Hbit.
  destruct (N.testbit S (N.log2 (N.land S T))) eqn:HS;
    destruct (N.testbit T (N.log2 (N.land S T))) eqn:HT;
    try discriminate.
  split; assumption.
Qed.

(*
│
│          When `S<2^k`, any overlap involving `S` must occur below
│          index `k`.
│
*)

(*                        S<2ᵏ ∧ Overlap(S,T,i) ⇒ i<k                         *)

Lemma bit_overlap_index_lt_pow2 :
  forall k S T i,
    S < 2 ^ k ->
    bit_overlap S T i ->
    i < k.
Proof.
  intros k S T i HS [HSi _].
  destruct (N.lt_ge_cases i k) as [Hlt|Hge].
  - exact Hlt.
  - pose proof (CC.lt_pow2_bits_false S k i HS Hge) as Hfalse.
    rewrite HSi in Hfalse.
    discriminate.
Qed.

(*
│
│          For operands below `2^k`, carrylessness is equivalent to no
│          overlap inside the finite `k`-window.
│
*)

(*              S,T<2ᵏ ⇒ carryless₂(S,T) ⇔ NoOverlapBelow(k,S,T)              *)

Lemma carryless2_iff_no_bit_overlap_below_pow2 :
  forall k S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    (carryless2 S T <-> no_bit_overlap_below k S T).
Proof.
  intros k S T HS HT.
  split.
  - intros Hcarry i _.
    apply carryless2_no_bit_overlap.
    exact Hcarry.
  - intro Hnone.
    apply no_bit_overlap_carryless2.
    intros i Hoverlap.
    apply (Hnone i).
    + apply bit_overlap_index_lt_pow2 with (S := S) (T := T).
      * exact HS.
      * exact Hoverlap.
    + exact Hoverlap.
Qed.

(*
│
│          A well-formed carryless binomial instance exposes its
│          power-of-two window and operand bounds.
│
*)

(*                    WF(B,S,T) ⇒ ∃ k. B=2ᵏ ∧ S<2ᵏ ∧ T<2ᵏ                     *)

Lemma carryless_binomial_wf_as_pow2_window :
  forall B S T,
    carryless_binomial_wf B S T ->
    exists k, B = 2 ^ k /\ S < 2 ^ k /\ T < 2 ^ k.
Proof.
  intros B S T [[k HB] [HS HT]].
  exists k.
  subst B.
  repeat split; assumption.
Qed.

(*
│
│          For a well-formed instance with `B=2^k`, carrylessness is
│          exactly no overlap below `k`.
│
*)

(*            WF ∧ B=2ᵏ ⇒ carryless₂(S,T) ⇔ NoOverlapBelow(k,S,T)             *)

Lemma carryless_binomial_wf_no_bit_overlap_window :
  forall B S T k,
    carryless_binomial_wf B S T ->
    B = 2 ^ k ->
    (carryless2 S T <-> no_bit_overlap_below k S T).
Proof.
  intros B S T k (_Hpow & HS & HT) HB.
  subst B.
  apply carryless2_iff_no_bit_overlap_below_pow2; assumption.
Qed.

(*
│
│          Adding a block shifted above the `k`-window does not change
│          the bitcount in the low `k`-window.
│
*)

(*                low<2ᵏ ⇒ Window(k,low+high·2ᵏ)=Window(k,low)                *)

Lemma bitcount_window_add_shift_low :
  forall k low high,
    low < 2 ^ k ->
    bitcount_window (N.to_nat k) (low + high * 2 ^ k) =
    bitcount_window (N.to_nat k) low.
Proof.
  intros k low high Hlow.
  apply bitcount_window_ext.
  intros i Hi.
  rewrite N2Nat.id in Hi.
  apply CC.add_shift_testbit_low; assumption.
Qed.

(*
│
│          The bitcount of a low-plus-shifted-high stack splits across
│          the low window and the high window.
│
*)

(*            Window(k+n,low+high·2ᵏ)=Window(k,low)+Window(n,high)            *)

Lemma bitcount_window_add_shift :
  forall k n low high,
    low < 2 ^ k ->
    bitcount_window (N.to_nat k + n)%nat (low + high * 2 ^ k) =
    bitcount_window (N.to_nat k) low + bitcount_window n high.
Proof.
  intros k n.
  induction n as [|n IH]; intros low high Hlow.
  - rewrite Nat.add_0_r.
    cbn [bitcount_window].
    rewrite N.add_0_r.
    apply bitcount_window_add_shift_low.
    exact Hlow.
  - rewrite Nat.add_succ_r.
    cbn [bitcount_window].
    rewrite IH by exact Hlow.
    rewrite CC.add_shift_testbit_high.
    + replace (N.of_nat (N.to_nat k + n) - k) with (N.of_nat n)
        by (rewrite Nat2N.inj_add, N2Nat.id; lia).
      lia.
    + exact Hlow.
    + rewrite Nat2N.inj_add, N2Nat.id.
      lia.
Qed.

(*
│
│          Xor contributes the sum of two bit values when the two
│          source bits are not both true.
│
*)

(*                      ¬(a∧b) ⇒ bit(a⊕b)=bit(a)+bit(b)                       *)

Lemma bit_value_lxor_no_overlap :
  forall a b,
    ~ (a = true /\ b = true) ->
    bit_value (xorb a b) = bit_value a + bit_value b.
Proof.
  destruct a, b; unfold bit_value; simpl; intuition lia.
Qed.

(*
│
│          If every bit of `y` is the complement of the corresponding
│          bit of `x` inside a window, their window bitcounts
│          complement to the window size.
│
*)

(*           ∀ i<n. bit(y,i)=1−bit(x,i) ⇒ Window(n,y)=n−Window(n,x)           *)

Lemma bitcount_window_complement_by_bits :
  forall n x y,
    (forall i,
      i < N.of_nat n ->
      bit_value (N.testbit y i) =
      1 - bit_value (N.testbit x i)) ->
    bitcount_window n y = N.of_nat n - bitcount_window n x.
Proof.
  induction n as [|n IH]; intros x y Hbits; cbn [bitcount_window].
  - reflexivity.
  - rewrite (IH x y).
    + rewrite Hbits by (rewrite Nat2N.inj_succ; lia).
      pose proof (bitcount_window_bound n x).
      rewrite Nat2N.inj_succ.
      destruct (N.testbit x (N.of_nat n)); unfold bit_value; lia.
    + intros i Hi.
      apply Hbits.
      rewrite Nat2N.inj_succ.
      lia.
Qed.

(*
│
│          A value below `2^k` has logarithm below `k` when `k` is
│          positive.
│
*)

(*                           0<k ∧ x<2ᵏ ⇒ log₂(x)<k                           *)

Lemma log2_lt_pow2_bound :
  forall k x,
    0 < k ->
    x < 2 ^ k ->
    N.log2 x < k.
Proof.
  intros k x Hk Hx.
  destruct (N.eq_0_gt_0_cases x) as [->|Hxpos].
  - simpl.
    lia.
  - apply (proj1 (N.log2_lt_pow2 x k Hxpos)).
    exact Hx.
Qed.

(*
│
│          Carryless addition makes finite-window bitcount additive.
│
*)

(*          carryless₂(S,T) ⇒ Window(n,S+T)=Window(n,S)+Window(n,T)           *)

Lemma bitcount_window_add_carryless :
  forall n S T,
    carryless2 S T ->
    bitcount_window n (S + T) =
    bitcount_window n S + bitcount_window n T.
Proof.
  induction n as [|n IH]; intros S T Hcarry; simpl.
  - lia.
  - rewrite IH by exact Hcarry.
    assert
      (Hbitadd :
        N.testbit (S + T) (N.of_nat n) =
        xorb (N.testbit S (N.of_nat n)) (N.testbit T (N.of_nat n))).
    {
      rewrite N.add_nocarry_lxor
        by (unfold carryless2 in Hcarry; exact Hcarry).
      rewrite N.lxor_spec.
      reflexivity.
    }
    rewrite Hbitadd.
    rewrite bit_value_lxor_no_overlap.
    + lia.
    + intro Hoverlap.
      apply (carryless2_no_bit_overlap S T (N.of_nat n) Hcarry).
      exact Hoverlap.
Qed.

(*
│
│          The carryless-addition bitcount identity specializes under
│          the bridge well-formedness hypotheses.
│
*)

(*    WF ∧ B=2ᵏ ∧ carryless₂(S,T) ⇒ Window(k,S+T)=Window(k,S)+Window(k,T)     *)

Lemma bitcount_window_add_carryless_under_wf :
  forall B S T k,
    carryless_binomial_wf B S T ->
    B = 2 ^ k ->
    carryless2 S T ->
    bitcount_window (N.to_nat k) (S + T) =
    bitcount_window (N.to_nat k) S + bitcount_window (N.to_nat k) T.
Proof.
  intros B S T k _Hwf _HB Hcarry.
  apply bitcount_window_add_carryless.
  exact Hcarry.
Qed.

(*
│
│          Adding one increases a finite-window bitcount by at most
│          one.
│
*)

(*                        Window(n,x+1)≤Window(n,x)+1                         *)

Lemma bitcount_window_add_one :
  forall n x,
    bitcount_window n (x + 1) <= bitcount_window n x + 1.
Proof.
  induction n as [|n IH]; intro x.
  - cbn [bitcount_window].
    lia.
  - rewrite (bitcount_window_succ_div2 n (x + 1)).
    rewrite (bitcount_window_succ_div2 n x).
    rewrite N.add_bit0.
    replace (N.testbit 1 0) with true by reflexivity.
    replace ((x + 1) / 2) with ((x + 0 + N.b2n true) / 2)
      by (cbn [N.b2n]; rewrite N.add_0_r; reflexivity).
    rewrite N.add_carry_div2.
    rewrite N.bits_0.
    change (0 / 2) with 0.
    destruct (N.testbit x 0); cbn [xorb andb orb N.b2n bit_value].
    + replace (x / 2 + 0 + 1) with (x / 2 + 1) by lia.
      pose proof (IH (x / 2)).
      lia.
    + replace (x / 2 + 0 + 0) with (x / 2) by lia.
      lia.
Qed.

(*
│
│          Halving a value below `2^(S n)` yields a value below `2^n`.
│
*)

(*                  x<2^(N.ofNat(S n)) ⇒ ⌊x÷2⌋<2^(N.ofNat n)                  *)

Lemma div2_bound_pow2_nat :
  forall n x,
    x < 2 ^ N.of_nat (S n) ->
    x / 2 < 2 ^ N.of_nat n.
Proof.
  intros n x Hx.
  apply (N.Private_NDivProp.div_lt_upper_bound x 2 (2 ^ N.of_nat n)).
  - lia.
  - rewrite Nat2N.inj_succ in Hx.
    rewrite N.pow_succ_r in Hx by lia.
    exact Hx.
Qed.

(*
│
│          Window bitcount of bounded addition is subadditive in the
│          successor window.
│
*)

(*      S,T<2^(N.ofNat n) ⇒ Window(succ(n),S+T)≤Window(n,S)+Window(n,T)       *)

Lemma bitcount_window_add_bound_pow2_nat :
  forall n S T,
    S < 2 ^ N.of_nat n ->
    T < 2 ^ N.of_nat n ->
    bitcount_window (Datatypes.S n) (S + T) <=
    bitcount_window n S + bitcount_window n T.
Proof.
  induction n as [|n IH]; intros S T HS HT.
  - assert (S = 0) by lia.
    assert (T = 0) by lia.
    subst S T.
    cbn [bitcount_window].
    rewrite N.bits_0.
    unfold bit_value.
    lia.
  - rewrite (bitcount_window_succ_div2 (Datatypes.S n) (S + T)).
    rewrite (bitcount_window_succ_div2 n S).
    rewrite (bitcount_window_succ_div2 n T).
    rewrite N.add_bit0.
    assert
      (Hdiv :
        (S + T) / 2 =
        S / 2 + T / 2 +
        N.b2n (N.testbit S 0 && N.testbit T 0)).
    {
      replace ((S + T) / 2) with ((S + T + N.b2n false) / 2)
        by (cbn [N.b2n]; rewrite N.add_0_r; reflexivity).
      rewrite N.add_carry_div2.
      cbn [N.b2n andb orb].
      rewrite Bool.orb_false_r.
      reflexivity.
    }
    rewrite Hdiv.
    pose proof (div2_bound_pow2_nat n S HS) as HSdiv.
    pose proof (div2_bound_pow2_nat n T HT) as HTdiv.
    pose proof (IH (S / 2) (T / 2) HSdiv HTdiv) as Hhigh.
    destruct (N.testbit S 0) eqn:HS0;
      destruct (N.testbit T 0) eqn:HT0;
      cbn [xorb andb N.b2n bit_value].
    + pose proof
        (bitcount_window_add_one (Datatypes.S n) (S / 2 + T / 2))
        as Hone.
      eapply N.le_trans.
      * exact Hone.
      * lia.
    + replace (S / 2 + T / 2 + 0) with (S / 2 + T / 2) by lia.
      lia.
    + replace (S / 2 + T / 2 + 0) with (S / 2 + T / 2) by lia.
      lia.
    + replace (S / 2 + T / 2 + 0) with (S / 2 + T / 2) by lia.
      lia.
Qed.

(*
│
│          If the low bits do not overlap and the halves are
│          carryless, then the original operands are carryless.
│
*)

(*        ¬Overlap(S,T,0) ∧ carryless₂(⌊S÷2⌋,⌊T÷2⌋) ⇒ carryless₂(S,T)         *)

Lemma carryless2_from_low_div2 :
  forall S T,
    ~ bit_overlap S T 0 ->
    carryless2 (S / 2) (T / 2) ->
    carryless2 S T.
Proof.
  intros S T Hlow Hhigh.
  apply no_bit_overlap_carryless2.
  intros i Hoverlap.
  destruct (N.eq_dec i 0) as [->|Hi0].
  - exact (Hlow Hoverlap).
  - apply (carryless2_no_bit_overlap (S / 2) (T / 2) (i - 1) Hhigh).
    destruct Hoverlap as [HS HT].
    split.
    + rewrite N.div2_bits.
      replace (N.succ (i - 1)) with i by lia.
      exact HS.
    + rewrite N.div2_bits.
      replace (N.succ (i - 1)) with i by lia.
      exact HT.
Qed.

(*
│
│          If bounded operands are not carryless, then addition
│          strictly drops the bitcount below the source bitcount sum.
│
*)

(*                   S,T<2^(N.ofNat n) ∧ ¬carryless₂(S,T) ⇒                   *)
(*                Window(succ(n),S+T)<Window(n,S)+Window(n,T)                 *)

Lemma bitcount_window_add_strict_overlap_pow2_nat :
  forall n S T,
    S < 2 ^ N.of_nat n ->
    T < 2 ^ N.of_nat n ->
    ~ carryless2 S T ->
    bitcount_window (Datatypes.S n) (S + T) <
    bitcount_window n S + bitcount_window n T.
Proof.
  induction n as [|n IH]; intros S T HS HT Hnot.
  - assert (S = 0) by lia.
    assert (T = 0) by lia.
    subst S T.
    exfalso.
    apply Hnot.
    unfold carryless2.
    reflexivity.
  - rewrite (bitcount_window_succ_div2 (Datatypes.S n) (S + T)).
    rewrite (bitcount_window_succ_div2 n S).
    rewrite (bitcount_window_succ_div2 n T).
    rewrite N.add_bit0.
    assert
      (Hdiv :
        (S + T) / 2 =
        S / 2 + T / 2 +
        N.b2n (N.testbit S 0 && N.testbit T 0)).
    {
      replace ((S + T) / 2) with ((S + T + N.b2n false) / 2)
        by (cbn [N.b2n]; rewrite N.add_0_r; reflexivity).
      rewrite N.add_carry_div2.
      cbn [N.b2n andb orb].
      rewrite Bool.orb_false_r.
      reflexivity.
    }
    rewrite Hdiv.
    pose proof (div2_bound_pow2_nat n S HS) as HSdiv.
    pose proof (div2_bound_pow2_nat n T HT) as HTdiv.
    destruct (N.testbit S 0) eqn:HS0;
      destruct (N.testbit T 0) eqn:HT0;
      cbn [xorb andb N.b2n bit_value].
    + pose proof
        (bitcount_window_add_bound_pow2_nat n (S / 2) (T / 2) HSdiv HTdiv)
        as Hbound.
      pose proof
        (bitcount_window_add_one (Datatypes.S n) (S / 2 + T / 2))
        as Hone.
      lia.
    + assert (Hhigh_not : ~ carryless2 (S / 2) (T / 2)).
      {
        intro Hhigh.
        apply Hnot.
        apply carryless2_from_low_div2.
        - intros [_ HTlow].
          rewrite HT0 in HTlow.
          discriminate.
        - exact Hhigh.
      }
      pose proof (IH (S / 2) (T / 2) HSdiv HTdiv Hhigh_not) as Hstrict.
      replace (S / 2 + T / 2 + 0) with (S / 2 + T / 2) by lia.
      lia.
    + assert (Hhigh_not : ~ carryless2 (S / 2) (T / 2)).
      {
        intro Hhigh.
        apply Hnot.
        apply carryless2_from_low_div2.
        - intros [HSlow _].
          rewrite HS0 in HSlow.
          discriminate.
        - exact Hhigh.
      }
      pose proof (IH (S / 2) (T / 2) HSdiv HTdiv Hhigh_not) as Hstrict.
      replace (S / 2 + T / 2 + 0) with (S / 2 + T / 2) by lia.
      lia.
    + assert (Hhigh_not : ~ carryless2 (S / 2) (T / 2)).
      {
        intro Hhigh.
        apply Hnot.
        apply carryless2_from_low_div2.
        - intros [HSlow _].
          rewrite HS0 in HSlow.
          discriminate.
        - exact Hhigh.
      }
      pose proof (IH (S / 2) (T / 2) HSdiv HTdiv Hhigh_not) as Hstrict.
      replace (S / 2 + T / 2 + 0) with (S / 2 + T / 2) by lia.
      lia.
Qed.

(*
│
│          For a value below `2^k`, extending the window from `k` to
│          `S k` does not change the bitcount.
│
*)

(*                      x<2ᵏ ⇒ Window(S k,x)=Window(k,x)                      *)

Lemma bitcount_window_succ_pow2_bound :
  forall k x,
    x < 2 ^ k ->
    bitcount_window (N.to_nat (N.succ k)) x =
    bitcount_window (N.to_nat k) x.
Proof.
  intros k x Hx.
  replace (N.to_nat (N.succ k)) with (S (N.to_nat k))
    by (rewrite N2Nat.inj_succ; reflexivity).
  cbn [bitcount_window].
  replace (N.of_nat (N.to_nat k)) with k by (symmetry; apply N2Nat.id).
  rewrite (CC.lt_pow2_bits_false x k k Hx) by lia.
  unfold bit_value.
  rewrite N.add_0_r.
  reflexivity.
Qed.

(*
│
│          The strict-overlap bitcount drop is restated for
│          binary-natural window exponents.
│
*)

(*    S,T<2ᵏ ∧ ¬carryless₂(S,T) ⇒ Window(S k,S+T)<Window(k,S)+Window(k,T)     *)

Lemma bitcount_window_add_strict_overlap_pow2 :
  forall k S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    ~ carryless2 S T ->
    bitcount_window (N.to_nat (N.succ k)) (S + T) <
    bitcount_window (N.to_nat k) S + bitcount_window (N.to_nat k) T.
Proof.
  intros k S T HS HT Hnot.
  pose proof
    (bitcount_window_add_strict_overlap_pow2_nat
      (N.to_nat k) S T) as Hstrict.
  rewrite N2Nat.id in Hstrict.
  replace (Datatypes.S (N.to_nat k)) with (N.to_nat (N.succ k)) in Hstrict
    by (rewrite N2Nat.inj_succ; reflexivity).
  apply Hstrict; assumption.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        BRIDGE SLOT DECOMPOSITION                        ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The low slot is the base complement of `T` below `B−1`.
│
*)

(*                               Low(B,T)=B−1−T                               *)

Definition bridge_low_slot (B T : N) : N :=
  B - 1 - T.

(*
│
│          The middle slot is the base complement of `S` below `B−1`.
│
*)

(*                               Mid(B,S)=B−1−S                               *)

Definition bridge_mid_slot (B S : N) : N :=
  B - 1 - S.

(*
│
│          The high slot is the ordinary sum `S+T`.
│
*)

(*                               High(S,T)=S+T                                *)

Definition bridge_high_slot (S T : N) : N :=
  S + T.

(*
│
│          A three-slot stack over a power-of-two window stores low,
│          middle, and high slots in consecutive windows.
│
*)

(*                       Stack₃(k,l,m,h)=l+(m+h·2ᵏ)·2ᵏ                        *)

Definition stack3_pow2 (k low mid high : N) : N :=
  low + (mid + high * 2 ^ k) * 2 ^ k.

(*
│
│          The slotted bridge value stores low complement, middle
│          complement, and high sum in base `B`.
│
*)

(*               RSlots(B,S,T)=Low(B,T)+Mid(B,S)·B+High(S,T)·B²               *)

Definition carryless_bridge_R_slots (B S T : N) : N :=
  bridge_low_slot B T +
  bridge_mid_slot B S * B +
  bridge_high_slot S T * carryless_square_modulus B.

(*
│
│          Slot boundedness records that low and middle slots fit
│          below `B`, while the high sum fits below `2B`.
│
*)

(*                   SlotsBounded ⇔ Low<B ∧ Mid<B ∧ High<2B                   *)

Definition bridge_slots_bounded (B S T : N) : Prop :=
  bridge_low_slot B T < B /\
  bridge_mid_slot B S < B /\
  bridge_high_slot S T < 2 * B.

(*
│
│          The power-of-two three-slot stack unfolds to low plus
│          middle times `2^k` plus high times `2^(2k)`.
│
*)

(*                      Stack₃(k,l,m,h)=l+m·2ᵏ+h·(2ᵏ·2ᵏ)                      *)

Lemma stack3_pow2_unfold :
  forall k low mid high,
    stack3_pow2 k low mid high =
    low + mid * 2 ^ k + high * (2 ^ k * 2 ^ k).
Proof.
  intros k low mid high.
  unfold stack3_pow2.
  nia.
Qed.

(*
│
│          The bitcount of a three-slot stack splits into low, middle,
│          and high windows when low and middle fit below `2^k`.
│
*)

(*      Window(k+k+n,Stack₃)=Window(k,low)+Window(k,mid)+Window(n,high)       *)

Lemma bitcount_window_stack3_pow2 :
  forall k n low mid high,
    low < 2 ^ k ->
    mid < 2 ^ k ->
    bitcount_window (N.to_nat k + (N.to_nat k + n))%nat
      (stack3_pow2 k low mid high) =
    bitcount_window (N.to_nat k) low +
    bitcount_window (N.to_nat k) mid +
    bitcount_window n high.
Proof.
  intros k n low mid high Hlow Hmid.
  unfold stack3_pow2.
  rewrite bitcount_window_add_shift by exact Hlow.
  rewrite bitcount_window_add_shift by exact Hmid.
  lia.
Qed.

(*
│
│          When the base is `2^k`, the slotted bridge value is the
│          corresponding three-slot stack.
│
*)

(*                   RSlots(2ᵏ,S,T)=Stack₃(k,Low,Mid,High)                    *)

Lemma carryless_bridge_R_slots_as_stack3_pow2 :
  forall k S T,
    carryless_bridge_R_slots (2 ^ k) S T =
    stack3_pow2 k
      (bridge_low_slot (2 ^ k) T)
      (bridge_mid_slot (2 ^ k) S)
      (bridge_high_slot S T).
Proof.
  intros k S T.
  unfold carryless_bridge_R_slots, stack3_pow2, carryless_square_modulus.
  nia.
Qed.

(*
│
│          The finite-window bitcount of the slotted bridge value
│          splits across its three slots.
│
*)

(*      Window(k+k+n,RSlots)=Window(k,Low)+Window(k,Mid)+Window(n,High)       *)

Lemma bitcount_window_bridge_R_slots_pow2 :
  forall k n S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    bitcount_window (N.to_nat k + (N.to_nat k + n))%nat
      (carryless_bridge_R_slots (2 ^ k) S T) =
    bitcount_window (N.to_nat k) (bridge_low_slot (2 ^ k) T) +
    bitcount_window (N.to_nat k) (bridge_mid_slot (2 ^ k) S) +
    bitcount_window n (bridge_high_slot S T).
Proof.
  intros k n S T HS HT.
  rewrite carryless_bridge_R_slots_as_stack3_pow2.
  apply bitcount_window_stack3_pow2.
  - unfold bridge_low_slot.
    lia.
  - unfold bridge_mid_slot.
    lia.
Qed.

(*
│
│          For a positive power-of-two window, the low slot is the
│          `k`-bit complement of `T`.
│
*)

(*                      0<k ∧ T<2ᵏ ⇒ Low(2ᵏ,T)=lnot(T,k)                      *)

Lemma bridge_low_slot_lnot_pow2 :
  forall k T,
    0 < k ->
    T < 2 ^ k ->
    bridge_low_slot (2 ^ k) T = N.lnot T k.
Proof.
  intros k T Hk HT.
  unfold bridge_low_slot.
  replace (2 ^ k - 1) with (N.ones k).
  - rewrite N.lnot_sub_low.
    + reflexivity.
    + apply log2_lt_pow2_bound; assumption.
  - rewrite N.ones_equiv.
    nia.
Qed.

(*
│
│          For a positive power-of-two window, the middle slot is the
│          `k`-bit complement of `S`.
│
*)

(*                      0<k ∧ S<2ᵏ ⇒ Mid(2ᵏ,S)=lnot(S,k)                      *)

Lemma bridge_mid_slot_lnot_pow2 :
  forall k S,
    0 < k ->
    S < 2 ^ k ->
    bridge_mid_slot (2 ^ k) S = N.lnot S k.
Proof.
  intros k S Hk HS.
  unfold bridge_mid_slot, bridge_low_slot in *.
  apply bridge_low_slot_lnot_pow2; assumption.
Qed.

(*
│
│          The low-slot bitcount complements the bitcount of `T`
│          inside the `k`-window.
│
*)

(*                  T<2ᵏ ⇒ Window(k,Low(2ᵏ,T))=k−Window(k,T)                  *)

Lemma bridge_low_slot_bitcount_complement_pow2 :
  forall k T,
    T < 2 ^ k ->
    bitcount_window (N.to_nat k) (bridge_low_slot (2 ^ k) T) =
    k - bitcount_window (N.to_nat k) T.
Proof.
  intros k T HT.
  destruct (N.eq_dec k 0) as [->|Hkneq].
  - reflexivity.
  - assert (Hk : 0 < k) by lia.
    rewrite bridge_low_slot_lnot_pow2 by assumption.
    rewrite (bitcount_window_complement_by_bits (N.to_nat k) T (N.lnot T k)).
    + rewrite N2Nat.id.
      reflexivity.
    + intros i Hi.
      rewrite N2Nat.id in Hi.
      rewrite N.lnot_spec_low by exact Hi.
      destruct (N.testbit T i); unfold bit_value; reflexivity.
Qed.

(*
│
│          The middle-slot bitcount complements the bitcount of `S`
│          inside the `k`-window.
│
*)

(*                  S<2ᵏ ⇒ Window(k,Mid(2ᵏ,S))=k−Window(k,S)                  *)

Lemma bridge_mid_slot_bitcount_complement_pow2 :
  forall k S,
    S < 2 ^ k ->
    bitcount_window (N.to_nat k) (bridge_mid_slot (2 ^ k) S) =
    k - bitcount_window (N.to_nat k) S.
Proof.
  intros k S HS.
  destruct (N.eq_dec k 0) as [->|Hkneq].
  - reflexivity.
  - assert (Hk : 0 < k) by lia.
    rewrite bridge_mid_slot_lnot_pow2 by assumption.
    rewrite (bitcount_window_complement_by_bits (N.to_nat k) S (N.lnot S k)).
    + rewrite N2Nat.id.
      reflexivity.
    + intros i Hi.
      rewrite N2Nat.id in Hi.
      rewrite N.lnot_spec_low by exact Hi.
      destruct (N.testbit S i); unfold bit_value; reflexivity.
Qed.

(*
│
│          The high slot `S+T` fits below `2^(S k)` when both operands
│          are below `2^k`.
│
*)

(*                         S,T<2ᵏ ⇒ High(S,T)<2^(S k)                         *)

Lemma bridge_high_slot_pow2_bound :
  forall k S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    bridge_high_slot S T < 2 ^ N.succ k.
Proof.
  intros k S T HS HT.
  unfold bridge_high_slot.
  rewrite N.pow_succ_r by lia.
  lia.
Qed.

(*
│
│          The slotted bridge bitcount profile is two complemented low
│          windows plus the high-slot window.
│
*)

(*    Window(k+k+n,RSlots)=(k−Window(k,T))+(k−Window(k,S))+Window(n,High)     *)

Lemma bitcount_window_bridge_R_slots_profile_pow2 :
  forall k n S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    bitcount_window (N.to_nat k + (N.to_nat k + n))%nat
      (carryless_bridge_R_slots (2 ^ k) S T) =
    (k - bitcount_window (N.to_nat k) T) +
    (k - bitcount_window (N.to_nat k) S) +
    bitcount_window n (bridge_high_slot S T).
Proof.
  intros k n S T HS HT.
  rewrite bitcount_window_bridge_R_slots_pow2 by assumption.
  rewrite bridge_low_slot_bitcount_complement_pow2 by exact HT.
  rewrite bridge_mid_slot_bitcount_complement_pow2 by exact HS.
  lia.
Qed.

(*
│
│          Choosing the high window as `S k` captures the full
│          bitcount of the high slot.
│
*)

(*      Window(k+k+S k,RSlots)=(k−Window(k,T))+(k−Window(k,S))+Pop(High)      *)

Lemma bitcount_window_bridge_R_slots_full_high_pow2 :
  forall k S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    bitcount_window
      (N.to_nat k + (N.to_nat k + N.to_nat (N.succ k)))%nat
      (carryless_bridge_R_slots (2 ^ k) S T) =
    (k - bitcount_window (N.to_nat k) T) +
    (k - bitcount_window (N.to_nat k) S) +
    full_bitcount (bridge_high_slot S T).
Proof.
  intros k S T HS HT.
  rewrite bitcount_window_bridge_R_slots_profile_pow2 by assumption.
  replace
    (bitcount_window (N.to_nat (N.succ k)) (bridge_high_slot S T))
    with (full_bitcount (bridge_high_slot S T)).
  - reflexivity.
  - symmetry.
    apply bitcount_window_full_under_pow2_bound.
    apply bridge_high_slot_pow2_bound; assumption.
Qed.

(*
│
│          A single stacked slot stays below `H·B` when the low digit
│          is below `B` and the high tail is below `H`.
│
*)

(*                   0<B ∧ low<B ∧ high<H ⇒ low+high·B<H·B                    *)

Lemma stack_slot_bound :
  forall B low high H,
    0 < B ->
    low < B ->
    high < H ->
    low + high * B < H * B.
Proof.
  intros B low high H HB Hlow Hhigh.
  nia.
Qed.

(*
│
│          A three-slot power-of-two stack stays below the combined
│          power bound.
│
*)

(*          low,mid<2ᵏ ∧ high<2ʰ ⇒ Stack₃(k,low,mid,high)<2^(k+k+h)           *)

Lemma stack3_pow2_bound :
  forall k h low mid high,
    low < 2 ^ k ->
    mid < 2 ^ k ->
    high < 2 ^ h ->
    stack3_pow2 k low mid high < 2 ^ (k + k + h).
Proof.
  intros k h low mid high Hlow Hmid Hhigh.
  unfold stack3_pow2.
  pose proof (CC.pow2_lower_bound k) as Hkpos.
  pose proof
    (stack_slot_bound
      (2 ^ k) mid high (2 ^ h)
      ltac:(lia) Hmid Hhigh) as Hrest.
  pose proof
    (stack_slot_bound
      (2 ^ k) low (mid + high * 2 ^ k) (2 ^ h * 2 ^ k)
      ltac:(lia) Hlow Hrest) as Hall.
  rewrite N.pow_add_r.
  rewrite N.pow_add_r.
  nia.
Qed.

(*
│
│          The slotted bridge value fits below the full three-slot
│          power bound.
│
*)

(*                    S,T<2ᵏ ⇒ RSlots(2ᵏ,S,T)<2^(k+k+S k)                     *)

Lemma carryless_bridge_R_slots_bound_pow2 :
  forall k S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    carryless_bridge_R_slots (2 ^ k) S T < 2 ^ (k + k + N.succ k).
Proof.
  intros k S T HS HT.
  rewrite carryless_bridge_R_slots_as_stack3_pow2.
  apply stack3_pow2_bound.
  - unfold bridge_low_slot.
    lia.
  - unfold bridge_mid_slot.
    lia.
  - apply bridge_high_slot_pow2_bound; assumption.
Qed.

(*
│
│          The full bitcount of the slotted bridge value has the
│          complemented-low plus high-slot profile.
│
*)

(*           Pop(RSlots)=(k−Window(k,T))+(k−Window(k,S))+Pop(High)            *)

Lemma full_bitcount_bridge_R_slots_profile_pow2 :
  forall k S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    full_bitcount (carryless_bridge_R_slots (2 ^ k) S T) =
    (k - bitcount_window (N.to_nat k) T) +
    (k - bitcount_window (N.to_nat k) S) +
    full_bitcount (bridge_high_slot S T).
Proof.
  intros k S T HS HT.
  symmetry.
  rewrite <- bitcount_window_bridge_R_slots_full_high_pow2 by assumption.
  rewrite <- (bitcount_window_full_under_pow2_bound
    (k + k + N.succ k)
    (carryless_bridge_R_slots (2 ^ k) S T)).
  - replace (N.to_nat (k + k + N.succ k))
      with (N.to_nat k + (N.to_nat k + N.to_nat (N.succ k)))%nat.
    + reflexivity.
    + repeat rewrite N2Nat.inj_add.
      lia.
  - apply carryless_bridge_R_slots_bound_pow2; assumption.
Qed.

(*
│
│          The low complement slot is below the base when `T` is below
│          the base.
│
*)

(*                              T<B ⇒ Low(B,T)<B                              *)

Lemma bridge_low_slot_bound :
  forall B T,
    T < B ->
    bridge_low_slot B T < B.
Proof.
  intros B T HT.
  unfold bridge_low_slot.
  lia.
Qed.

(*
│
│          The middle complement slot is below the base when `S` is
│          below the base.
│
*)

(*                              S<B ⇒ Mid(B,S)<B                              *)

Lemma bridge_mid_slot_bound :
  forall B S,
    S < B ->
    bridge_mid_slot B S < B.
Proof.
  intros B S HS.
  unfold bridge_mid_slot.
  lia.
Qed.

(*
│
│          The high slot is below `2B` when both operands are below
│          `B`.
│
*)

(*                            S,T<B ⇒ High(S,T)<2B                            *)

Lemma bridge_high_slot_bound :
  forall B S T,
    S < B ->
    T < B ->
    bridge_high_slot S T < 2 * B.
Proof.
  intros B S T HS HT.
  unfold bridge_high_slot.
  lia.
Qed.

(*
│
│          When `S` and `T` are carryless, the high-slot bitcount is
│          additive in every finite window.
│
*)

(*          carryless₂(S,T) ⇒ Window(n,High)=Window(n,S)+Window(n,T)          *)

Lemma bridge_high_slot_bitcount_additive_carryless :
  forall n S T,
    carryless2 S T ->
    bitcount_window n (bridge_high_slot S T) =
    bitcount_window n S + bitcount_window n T.
Proof.
  intros n S T Hcarry.
  unfold bridge_high_slot.
  apply bitcount_window_add_carryless.
  exact Hcarry.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        KUMMER-STYLE FACTORIZATION                       ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The central-binomial bitcount bridge is repeated locally as
│          the external proposition needed for the final binomial
│          handoff.
│
*)

(*              CentralBridge ≔ ∀ R m. 2ᵐ∣Central(R) ⇔ m≤Pop(R)               *)

Definition central_binomial_bitcount_bridge : Prop :=
  forall R m,
    dividesN (2 ^ m) (central_binomial R) <->
    m <= full_bitcount R.

(*
│
│          The project-local threshold says the bridge value has at
│          least `2k` one-bits exactly when `S` and `T` are carryless.
│
*)

(*               WF ∧ B=2ᵏ ⇒ carryless₂(S,T) ⇔ 2k≤Pop(R(B,S,T))               *)

Definition carryless_bridge_R_bitcount_threshold : Prop :=
  forall B S T k,
    carryless_binomial_wf B S T ->
    B = 2 ^ k ->
    (carryless2 S T <->
     k + k <= full_bitcount (carryless_bridge_R B S T)).

(*
│
│          The final carryless binomial bridge follows conditionally
│          from the central-binomial bitcount bridge and the
│          project-local threshold theorem.
│
*)

(*            CentralBridge ∧ Threshold ⇒ CarrylessBinomialBridge             *)

Theorem carryless_binomial_bridge_from_bitcount_bridges :
  central_binomial_bitcount_bridge ->
  carryless_bridge_R_bitcount_threshold ->
  carryless_binomial_bridge.
Proof.
  intros Hcentral Hthreshold.
  split.
  - intros B S T Hwf Hcarry.
    destruct Hwf as [[k HB] [HS HT]].
    subst B.
    unfold carryless_binomial_target, carryless_square_modulus.
    rewrite <- N.pow_add_r.
    apply (proj2 (Hcentral (carryless_bridge_R (2 ^ k) S T) (k + k))).
    pose proof
      (proj1
        (Hthreshold
          (2 ^ k) S T k
          (conj (ex_intro _ k eq_refl) (conj HS HT))
          eq_refl)
        Hcarry) as Hbits.
    exact Hbits.
  - intros B S T Hwf Htarget.
    destruct Hwf as [[k HB] [HS HT]].
    subst B.
    apply
      (proj2
        (Hthreshold
          (2 ^ k) S T k
          (conj (ex_intro _ k eq_refl) (conj HS HT))
          eq_refl)).
    apply (proj1 (Hcentral (carryless_bridge_R (2 ^ k) S T) (k + k))).
    unfold carryless_binomial_target, carryless_square_modulus in Htarget.
    rewrite <- N.pow_add_r in Htarget.
    exact Htarget.
Qed.

(*
│
│          Under operand bounds, the original bridge value is equal to
│          its three-slot decomposition.
│
*)

(*                       S,T<B ⇒ R(B,S,T)=RSlots(B,S,T)                       *)

Lemma carryless_bridge_R_slot_decomposition :
  forall B S T,
    S < B ->
    T < B ->
    carryless_bridge_R B S T = carryless_bridge_R_slots B S T.
Proof.
  intros B S T HS HT.
  unfold carryless_bridge_R_slots,
    bridge_low_slot, bridge_mid_slot, bridge_high_slot,
    carryless_bridge_R, carryless_square_modulus.
  nia.
Qed.

(*
│
│          Well-formedness is enough to rewrite the bridge value into
│          slotted form.
│
*)

(*                     WF(B,S,T) ⇒ R(B,S,T)=RSlots(B,S,T)                     *)

Lemma carryless_bridge_R_slots_under_wf :
  forall B S T,
    carryless_binomial_wf B S T ->
    carryless_bridge_R B S T = carryless_bridge_R_slots B S T.
Proof.
  intros B S T (_Hpow & HS & HT).
  apply carryless_bridge_R_slot_decomposition; assumption.
Qed.

(*
│
│          Well-formedness implies all three bridge slots satisfy
│          their slot bounds.
│
*)

(*                      WF(B,S,T) ⇒ SlotsBounded(B,S,T)                       *)

Lemma bridge_slots_bounded_under_wf :
  forall B S T,
    carryless_binomial_wf B S T ->
    bridge_slots_bounded B S T.
Proof.
  intros B S T (_Hpow & HS & HT).
  unfold bridge_slots_bounded.
  repeat split.
  - apply bridge_low_slot_bound.
    exact HT.
  - apply bridge_mid_slot_bound.
    exact HS.
  - apply bridge_high_slot_bound; assumption.
Qed.

(*
│
│          Well-formedness packages both the slot decomposition and
│          the slot bounds.
│
*)

(*                        WF ⇒ R=RSlots ∧ SlotsBounded                        *)

Lemma carryless_bridge_R_slot_profile_under_wf :
  forall B S T,
    carryless_binomial_wf B S T ->
    carryless_bridge_R B S T = carryless_bridge_R_slots B S T /\
    bridge_slots_bounded B S T.
Proof.
  intros B S T Hwf.
  split.
  - apply carryless_bridge_R_slots_under_wf.
    exact Hwf.
  - apply bridge_slots_bounded_under_wf.
    exact Hwf.
Qed.

(*
│
│          The high-slot threshold isolates the only carry-sensitive
│          part of the bridge bitcount profile.
│
*)

(*        S,T<2ᵏ ⇒ carryless₂(S,T) ⇔ Window(k,S)+Window(k,T)≤Pop(High)        *)

Definition bridge_high_slot_bitcount_threshold : Prop :=
  forall k S T,
    S < 2 ^ k ->
    T < 2 ^ k ->
    (carryless2 S T <->
     bitcount_window (N.to_nat k) S +
     bitcount_window (N.to_nat k) T <=
     full_bitcount (bridge_high_slot S T)).

(*
│
│          The full bridge threshold follows from the high-slot
│          threshold plus the low and middle complement slots.
│
*)

(*                         HighThreshold ⇒ Threshold                          *)

Theorem carryless_bridge_R_bitcount_threshold_from_high_slot :
  bridge_high_slot_bitcount_threshold ->
  carryless_bridge_R_bitcount_threshold.
Proof.
  intros Hhigh B S T k (_Hpow & HS & HT) HB.
  subst B.
  rewrite carryless_bridge_R_slot_decomposition by assumption.
  rewrite full_bitcount_bridge_R_slots_profile_pow2 by assumption.
  pose proof (bitcount_window_bound (N.to_nat k) S) as HScount.
  pose proof (bitcount_window_bound (N.to_nat k) T) as HTcount.
  rewrite N2Nat.id in HScount, HTcount.
  specialize (Hhigh k S T HS HT) as [Hhigh_fwd Hhigh_rev].
  split.
  - intro Hcarry.
    apply Hhigh_fwd in Hcarry.
    lia.
  - intro Hbits.
    apply Hhigh_rev.
    lia.
Qed.

(*
│
│          The high-slot threshold is proved from additive bitcount
│          for carryless addition and strict bitcount drop for
│          overlapping addition.
│
*)

(*        S,T<2ᵏ ⇒ carryless₂(S,T) ⇔ Window(k,S)+Window(k,T)≤Pop(S+T)         *)

Theorem bridge_high_slot_bitcount_threshold_proved :
  bridge_high_slot_bitcount_threshold.
Proof.
  unfold bridge_high_slot_bitcount_threshold.
  intros k S T HS HT.
  assert
    (Hfull :
      full_bitcount (bridge_high_slot S T) =
      bitcount_window (N.to_nat (N.succ k)) (bridge_high_slot S T)).
  {
    symmetry.
    apply bitcount_window_full_under_pow2_bound.
    apply bridge_high_slot_pow2_bound; assumption.
  }
  rewrite Hfull.
  split.
  - intro Hcarry.
    rewrite bridge_high_slot_bitcount_additive_carryless by exact Hcarry.
    rewrite !bitcount_window_succ_pow2_bound by assumption.
    lia.
  - intro Hbits.
    destruct (N.eq_dec (N.land S T) 0) as [Hcarry|Hnot_eq].
    + unfold carryless2.
      exact Hcarry.
    + exfalso.
      assert (Hnot : ~ carryless2 S T).
      {
        unfold carryless2.
        exact Hnot_eq.
      }
      pose proof
        (bitcount_window_add_strict_overlap_pow2 k S T HS HT Hnot)
        as Hstrict.
      unfold bridge_high_slot in Hbits.
      lia.
Qed.

(*
│
│          The project-local threshold theorem is closed here,
│          independently of the central-binomial bitcount bridge.
│
*)

(*                                 Threshold                                  *)

Theorem carryless_bridge_R_bitcount_threshold_proved :
  carryless_bridge_R_bitcount_threshold.
Proof.
  apply carryless_bridge_R_bitcount_threshold_from_high_slot.
  exact bridge_high_slot_bitcount_threshold_proved.
Qed.
