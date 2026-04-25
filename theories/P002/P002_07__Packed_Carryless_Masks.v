(*P002_07__Packed_Carryless_Masks.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / P002_07__Packed_Carryless_Masks                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer collects the packed-trace arithmetic infrastructure: binary
  no-carry predicates, fixed-channel base decoding, and carryless masks for
  digit bounds.

  The scope remains semantic and local. It does not define FM transitions,
  trace validity, cubic families, or terminal target equations. Later
  packed-step files consume this layer through decoded views and
  mask-correctness lemmas.

*)

(*
│
│          This file uses Boolean tests, binary naturals, and linear
│          arithmetic for bit-level mask proofs.
│
*)

(*                              Bool ∧ ℕ₂ ∧ lia                               *)

From Stdlib Require Import Bool NArith Lia.

(*
│
│          The packed-mask layer imports the cubic-family core only
│          for the encoded-state and machine-state record interfaces.
│
*)

(*                            P002₀₃ → PackedMasks                            *)

From P002 Require Import P002_03__Witness_Family_Core.

Local Open Scope N_scope.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                              CARRYLESS CORE                             ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          A base is a binary power when it is exactly `2^k` for some
│          exponent.
│
*)

(*                            pow₂(B) ⇔ ∃ k. B=2ᵏ                             *)

Definition pow2 (B : N) : Prop :=
  exists k, B = 2 ^ k.

(*
│
│          Two numbers are carryless when their binary supports are
│          disjoint.
│
*)

(*                       carryless₂(S,T) ⇔ S ∧bits T=0                        *)

Definition carryless2 (S T : N) : Prop :=
  N.land S T = 0.

(*
│
│          Every binary power is at least one.
│
*)

(*                                    1≤2ⁿ                                    *)

Lemma pow2_lower_bound :
  forall n,
    1 <= 2 ^ n.
Proof.
  intro n.
  apply N.pow_lower_bound.
  discriminate.
Qed.

(*
│
│          Bits at positions beyond the width of a value below `2^n`
│          are false.
│
*)

(*                          x<2ⁿ ∧ n≤m ⇒ bit(x,m)=0                           *)

Lemma lt_pow2_bits_false :
  forall x n m,
    x < 2 ^ n ->
    n <= m ->
    N.testbit x m = false.
Proof.
  intros x n m Hx Hnm.
  destruct (N.eq_0_gt_0_cases x) as [->|Hxpos].
  - apply N.bits_0.
  - apply (proj1 (N.log2_lt_pow2 x n Hxpos)) in Hx.
    apply N.bits_above_log2.
    lia.
Qed.

(*
│
│          A low block below `2^n` is carryless from any block shifted
│          upward by `n` bits.
│
*)

(*                         a<2ⁿ ⇒ carryless₂(a,b·2ⁿ)                          *)

Lemma carryless_low_high :
  forall a b n,
    a < 2 ^ n ->
    carryless2 a (b * 2 ^ n).
Proof.
  intros a b n Ha.
  unfold carryless2.
  apply N.bits_inj_0.
  intro m.
  rewrite N.land_spec.
  destruct (N.lt_ge_cases m n) as [Hmn|Hmn].
  - rewrite N.mul_pow2_bits_low by exact Hmn.
    destruct (N.testbit a m); reflexivity.
  - rewrite (lt_pow2_bits_false a n m Ha Hmn).
    destruct (N.testbit (b * 2 ^ n) m); reflexivity.
Qed.

(*
│
│          Below the split point, adding a high shifted block leaves
│          the low bits unchanged.
│
*)

(*                        m<n ⇒ bit(a+b·2ⁿ,m)=bit(a,m)                        *)

Lemma add_shift_testbit_low :
  forall a b n m,
    a < 2 ^ n ->
    m < n ->
    N.testbit (a + b * 2 ^ n) m = N.testbit a m.
Proof.
  intros a b n m Ha Hm.
  rewrite N.add_nocarry_lxor by (apply carryless_low_high; exact Ha).
  rewrite N.lxor_spec.
  rewrite N.mul_pow2_bits_low by exact Hm.
  destruct (N.testbit a m); reflexivity.
Qed.

(*
│
│          At and above the split point, adding a shifted high block
│          exposes the high block bits.
│
*)

(*                       n≤m ⇒ bit(a+b·2ⁿ,m)=bit(b,m−n)                       *)

Lemma add_shift_testbit_high :
  forall a b n m,
    a < 2 ^ n ->
    n <= m ->
    N.testbit (a + b * 2 ^ n) m = N.testbit b (m - n).
Proof.
  intros a b n m Ha Hm.
  rewrite N.add_nocarry_lxor by (apply carryless_low_high; exact Ha).
  rewrite N.lxor_spec.
  rewrite (lt_pow2_bits_false a n m Ha Hm).
  rewrite N.mul_pow2_bits_high by exact Hm.
  destruct (N.testbit b (m - n)); reflexivity.
Qed.

(*
│
│          The gap between two binary powers is the contiguous mask
│          between their exponents.
│
*)

(*                          m≤k ⇒ 2ᵏ−2ᵐ=ones(k−m)·2ᵐ                          *)

Lemma pow2_gap_as_mask :
  forall k m,
    m <= k ->
    2 ^ k - 2 ^ m = N.ones (k - m) * 2 ^ m.
Proof.
  intros k m Hmk.
  assert (Hsplit : (k - m + m)%N = k).
  { apply N.sub_add. exact Hmk. }
  rewrite <- Hsplit at 1.
  rewrite N.pow_add_r.
  rewrite (N.mul_comm (N.ones (k - m)) (2 ^ m)).
  rewrite N.ones_equiv.
  rewrite N.mul_pred_r.
  rewrite (N.mul_comm (2 ^ m) (2 ^ (k - m))).
  reflexivity.
Qed.

(*
│
│          The bit support of `2^k − 2^m` is exactly the half-open
│          interval from `m` to `k`.
│
*)

(*                        m<k ⇒ bit(2ᵏ−2ᵐ,n)=1 ⇔ m≤n<k                        *)

Lemma pow2_gap_bits :
  forall k m n,
    m < k ->
    N.testbit (2 ^ k - 2 ^ m) n = true <->
    m <= n < k.
Proof.
  intros k m n Hmk.
  rewrite pow2_gap_as_mask by lia.
  destruct (N.lt_ge_cases n m) as [Hnm|Hnm].
  - rewrite N.mul_pow2_bits_low by exact Hnm.
    split; intro H.
    + discriminate.
    + lia.
  - rewrite N.mul_pow2_bits_high by exact Hnm.
  rewrite N.ones_spec_iff.
  split; intro H; lia.
Qed.

(*
│
│          A value below a power-of-two base is below a smaller
│          power-of-two bound exactly when it is carryless from the
│          complementary bound mask.
│
*)

(*         pow₂(B) ∧ pow₂(b) ∧ b<B ∧ v<B ⇒ (v<b ⇔ carryless₂(B−b,v))          *)

Theorem carryless_bound_iff :
  forall B b v,
    pow2 B ->
    pow2 b ->
    b < B ->
    v < B ->
    (v < b <-> carryless2 (B - b) v).
Proof.
  intros B b v [k ->] [m ->] Hbk Hvb.
  assert (Hmk : m < k).
  {
    assert (Hiff : m < k <-> 2 ^ m < 2 ^ k).
    { apply N.pow_lt_mono_r_iff. lia. }
    apply (proj2 Hiff).
    exact Hbk.
  }
  split.
  - intro Hvm.
    unfold carryless2.
    apply N.bits_inj_0.
    intro n.
    rewrite N.land_spec.
    destruct (N.lt_ge_cases n m) as [Hnm|Hnm].
    + rewrite pow2_gap_as_mask by lia.
      rewrite N.mul_pow2_bits_low by exact Hnm.
      reflexivity.
    + rewrite (lt_pow2_bits_false v m n Hvm Hnm).
      destruct (N.testbit (2 ^ k - 2 ^ m) n); reflexivity.
  - intro Hcarry.
    destruct (N.ltb_spec v (2 ^ m)) as [Hvm|Hvm].
    + exact Hvm.
    + assert (Hvpos : 0 < v).
      {
        assert (Hpow : 1 <= 2 ^ m) by apply pow2_lower_bound.
        lia.
      }
      assert (Hlogk : N.log2 v < k).
      {
        apply (proj1 (N.log2_lt_pow2 v k Hvpos)).
        exact Hvb.
      }
      assert (Hmle : m <= N.log2 v).
      {
        destruct (N.lt_ge_cases (N.log2 v) m) as [Hlt|Hge].
        - pose proof (proj2 (N.log2_lt_pow2 v m Hvpos) Hlt) as Hcontra.
          lia.
        - exact Hge.
      }
      assert (Hbitv : N.testbit v (N.log2 v) = true).
      {
        apply N.bit_log2.
        apply (proj2 (N.neq_0_lt_0 v)).
        exact Hvpos.
      }
      assert (Hbitgap : N.testbit (2 ^ k - 2 ^ m) (N.log2 v) = true).
      {
        apply (proj2 (pow2_gap_bits k m (N.log2 v) Hmk)).
        lia.
      }
      assert (Hland : N.testbit (N.land (2 ^ k - 2 ^ m) v) (N.log2 v) = false).
      {
        rewrite Hcarry.
        apply N.bits_0.
      }
      rewrite N.land_spec in Hland.
      rewrite Hbitgap, Hbitv in Hland.
      discriminate.
Qed.

(*
│
│          Shifting two carryless values by the same binary offset
│          preserves carrylessness.
│
*)

(*                  carryless₂(S,T) ⇒ carryless₂(S·2ⁿ,T·2ⁿ)                   *)

Theorem carryless_shift :
  forall S T n,
    carryless2 S T ->
    carryless2 (S * 2 ^ n) (T * 2 ^ n).
Proof.
  intros S T n Hcarry.
  unfold carryless2 in *.
  apply N.bits_inj_0.
  intro m.
  rewrite N.land_spec.
  destruct (N.lt_ge_cases m n) as [Hmn|Hmn].
  - rewrite !N.mul_pow2_bits_low by exact Hmn.
    reflexivity.
  - rewrite !N.mul_pow2_bits_high by exact Hmn.
    rewrite <- N.land_spec.
    rewrite Hcarry.
    apply N.bits_0.
Qed.

(*
│
│          Stacking two low blocks and two high blocks preserves
│          carrylessness when each corresponding pair is carryless.
│
*)

(*         low<2ⁿ ∧ carryless₂(low₁,low₂) ∧ carryless₂(high₁,high₂) ⇒         *)
(*                  carryless₂(low₁+high₁·2ⁿ,low₂+high₂·2ⁿ)                   *)

Lemma carryless_stack_pow2 :
  forall n S1 T1 S2 T2,
    S1 < 2 ^ n ->
    T1 < 2 ^ n ->
    carryless2 S1 T1 ->
    carryless2 S2 T2 ->
    carryless2 (S1 + S2 * 2 ^ n) (T1 + T2 * 2 ^ n).
Proof.
  intros n S1 T1 S2 T2 HS1 HT1 Hlow Hhigh.
  unfold carryless2 in *.
  apply N.bits_inj_0.
  intro m.
  rewrite N.land_spec.
  destruct (N.lt_ge_cases m n) as [Hmn|Hmn].
  - rewrite (add_shift_testbit_low S1 S2 n m HS1 Hmn).
    rewrite (add_shift_testbit_low T1 T2 n m HT1 Hmn).
    rewrite <- N.land_spec.
    rewrite Hlow.
    apply N.bits_0.
  - rewrite (add_shift_testbit_high S1 S2 n m HS1 Hmn).
    rewrite (add_shift_testbit_high T1 T2 n m HT1 Hmn).
    rewrite <- N.land_spec.
    rewrite Hhigh.
    apply N.bits_0.
Qed.

(*
│
│          The stacking law also holds when the split base is supplied
│          abstractly as a binary power.
│
*)

(*      pow₂(N) ∧ S₁<N ∧ T₁<N ∧ carryless₂(S₁,T₁) ∧ carryless₂(S₂,T₂) ⇒       *)
(*                        carryless₂(S₁+S₂·N,T₁+T₂·N)                         *)

Theorem carryless_stack_2 :
  forall N S1 T1 S2 T2,
    pow2 N ->
    S1 < N ->
    T1 < N ->
    carryless2 S1 T1 ->
    carryless2 S2 T2 ->
    carryless2 (S1 + S2 * N) (T1 + T2 * N).
Proof.
  intros N S1 T1 S2 T2 [n ->] HS1 HT1 Hlow Hhigh.
  apply carryless_stack_pow2; assumption.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                            PACKED TRACE CODEC                           ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          A packed trace stores encoded machine states as the
│          state-code type used by the witness-family core.
│
*)

(*                          StateCode ≔ EncodedState                          *)

Definition FMStateCode : Type := EncodedState.

(*
│
│          Packed trace parameters fix the channel base, horizon, and
│          cell bound, with power-of-two and strict-bound side
│          conditions.
│
*)

(*                       Params=(B,H,C) ∧ pow₂(B) ∧ C<B                       *)

Record packed_trace_params : Type := {
  pt_base : N;
  pt_horizon : nat;
  pt_cell_bound : N;
  pt_base_pow2 : pow2 pt_base;
  pt_cell_bound_lt_base : pt_cell_bound < pt_base
}.

(*
│
│          A packed trace valuation has one channel for each semantic
│          stream: full state code, instruction pointer, two
│          registers, and halt bit.
│
*)

(*                         Vars=(state,ip,r₁,r₂,halt)                         *)

Record packed_trace_vars : Type := {
  pt_state_ch : N;
  pt_ip_ch : N;
  pt_r1_ch : N;
  pt_r2_ch : N;
  pt_halt_ch : N
}.

(*
│
│          The packed trace surface uses five semantic channels.
│
*)

(*                              PackedVarCount=5                              *)

Definition packed_trace_var_count : nat := 5%nat.

(*
│
│          The fixed channel count reduces definitionally to five.
│
*)

(*                              PackedVarCount=5                              *)

Lemma packed_trace_var_count_fixed :
  packed_trace_var_count = 5%nat.
Proof.
  reflexivity.
Qed.

(*
│
│          The fixed channel count is independent of the packed
│          parameter record.
│
*)

(*                           ∀ p. PackedVarCount=5                            *)

Lemma packed_trace_var_count_constant :
  forall p : packed_trace_params,
    packed_trace_var_count = 5%nat.
Proof.
  intro p.
  reflexivity.
Qed.

(*
│
│          The `t`-th base power is the positional weight for channel
│          digit `t`.
│
*)

(*                              BasePow(B,t)=Bᵗ                               *)

Definition base_pow (B : N) (t : nat) : N :=
  B ^ N.of_nat t.

(*
│
│          Digit extraction divides by the positional weight and takes
│          the remainder modulo the base.
│
*)

(*                         Digit(B,X,t)=⌊X÷Bᵗ⌋ mod B                          *)

Definition digit_at (B X : N) (t : nat) : N :=
  (X / base_pow B t) mod B.

(*
│
│          A channel packs a stream when every digit below the horizon
│          equals the corresponding stream value.
│
*)

(*              PacksChannel(B,H,x,X) ⇔ ∀ t<H. Digit(B,X,t)=x(t)              *)

Definition packs_channel
    (B : N) (horizon : nat) (xs : nat -> N) (X : N) : Prop :=
  forall t, (t < horizon)%nat -> digit_at B X t = xs t.

(*
│
│          Packing from an offset recursively writes the current digit
│          and shifts the remaining suffix by one base position.
│
*)

(*               PackFrom(B,s,S n,x)=x(s)+B·PackFrom(B,s+1,n,x)               *)

Fixpoint pack_channel_value_from
    (B : N) (start horizon : nat) (xs : nat -> N) : N :=
  match horizon with
  | O => 0
  | S horizon' =>
      xs start + B * pack_channel_value_from B (S start) horizon' xs
  end.

(*
│
│          A whole channel value is the packed stream starting at
│          offset zero.
│
*)

(*                       Pack(B,H,x)=PackFrom(B,0,H,x)                        *)

Definition pack_channel_value
    (B : N) (horizon : nat) (xs : nat -> N) : N :=
  pack_channel_value_from B 0 horizon xs.

(*
│
│          A binary power base is nonzero.
│
*)

(*                               pow₂(B) ⇒ B≠0                                *)

Lemma pow2_nonzero :
  forall B,
    pow2 B ->
    B <> 0.
Proof.
  intros B [k ->].
  apply N.pow_nonzero.
  lia.
Qed.

(*
│
│          The zeroth base power is one.
│
*)

(*                                    B⁰=1                                    *)

Lemma base_pow_0 :
  forall B,
    base_pow B 0 = 1.
Proof.
  intro B.
  unfold base_pow.
  change (B ^ 0 = 1).
  apply N.pow_0_r.
Qed.

(*
│
│          Successor base powers multiply the previous power by the
│          base.
│
*)

(*                       BasePow(B,S t)=B·BasePow(B,t)                        *)

Lemma base_pow_succ :
  forall B t,
    base_pow B (S t) = B * base_pow B t.
Proof.
  intros B t.
  unfold base_pow.
  rewrite Nat2N.inj_succ.
  rewrite N.pow_succ_r by lia.
  reflexivity.
Qed.

(*
│
│          Every positional weight over a binary power base is
│          nonzero.
│
*)

(*                               pow₂(B) ⇒ Bᵗ≠0                               *)

Lemma base_pow_nonzero :
  forall B t,
    pow2 B ->
    base_pow B t <> 0.
Proof.
  intros B t Hpow.
  unfold base_pow.
  apply N.pow_nonzero.
  now apply pow2_nonzero.
Qed.

(*
│
│          The lowest digit of a cons-style packed channel is the head
│          digit.
│
*)

(*                          x<B ⇒ Digit(B,x+B·Y,0)=x                          *)

Lemma digit_at_cons_zero :
  forall B x Y,
    x < B ->
    digit_at B (x + B * Y) 0 = x.
Proof.
  intros B x Y Hx.
  unfold digit_at.
  rewrite base_pow_0.
  rewrite N.div_1_r.
  rewrite (N.mul_comm B Y).
  rewrite N.Div0.mod_add.
  rewrite N.mod_small by exact Hx.
  reflexivity.
Qed.

(*
│
│          After the lowest digit, digit extraction from a cons-style
│          packed channel shifts to the tail.
│
*)

(*                      Digit(B,x+B·Y,S t)=Digit(B,Y,t)                       *)

Lemma digit_at_cons_succ :
  forall B x Y t,
    pow2 B ->
    x < B ->
    digit_at B (x + B * Y) (S t) = digit_at B Y t.
Proof.
  intros B x Y t Hpow Hx.
  unfold digit_at.
  rewrite base_pow_succ.
  rewrite <- (N.Div0.div_div (x + B * Y) B (base_pow B t)).
  assert (Hquot : (x + B * Y) / B = Y).
  {
    rewrite (N.mul_comm B Y).
    rewrite N.div_add by (apply pow2_nonzero; exact Hpow).
    rewrite N.div_small by exact Hx.
    lia.
  }
  rewrite Hquot.
  reflexivity.
Qed.

(*
│
│          Recursive packing recovers the source stream at every digit
│          below its local horizon.
│
*)

(*                 t<H ⇒ Digit(B,PackFrom(B,s,H,x),t)=x(s+t)                  *)

Lemma pack_channel_value_from_digit :
  forall B start horizon xs t,
    pow2 B ->
    (forall i, (i < horizon)%nat -> xs (start + i)%nat < B) ->
    (t < horizon)%nat ->
    digit_at B (pack_channel_value_from B start horizon xs) t =
    xs (start + t)%nat.
Proof.
  intros B start horizon.
  revert start.
  induction horizon as [|h IH]; intros start xs t Hpow Hbound Ht.
  - lia.
  - simpl in Ht.
    simpl pack_channel_value_from.
    destruct t as [|t'].
    + rewrite digit_at_cons_zero.
      * rewrite Nat.add_0_r.
        reflexivity.
      * replace start with (start + 0)%nat by lia.
        apply (Hbound 0%nat).
        lia.
    + rewrite digit_at_cons_succ.
      * replace (start + S t')%nat with (S start + t')%nat by lia.
        apply IH.
        -- exact Hpow.
        -- intros i Hi.
           replace (S start + i)%nat with (start + S i)%nat by lia.
           apply Hbound.
           lia.
        -- lia.
      * exact Hpow.
      * replace start with (start + 0)%nat by lia.
        apply (Hbound 0%nat).
        lia.
Qed.

(*
│
│          Whole-channel packing recovers the source stream at every
│          digit below the horizon.
│
*)

(*                     t<H ⇒ Digit(B,Pack(B,H,x),t)=x(t)                      *)

Lemma pack_channel_value_digit :
  forall B horizon xs t,
    pow2 B ->
    (forall i, (i < horizon)%nat -> xs i < B) ->
    (t < horizon)%nat ->
    digit_at B (pack_channel_value B horizon xs) t = xs t.
Proof.
  intros B horizon xs t Hpow Hbound Ht.
  unfold pack_channel_value.
  replace (0 + t)%nat with t by lia.
  apply (pack_channel_value_from_digit B 0 horizon xs t Hpow).
  - intros i Hi.
    replace (0 + i)%nat with i by lia.
    apply Hbound.
    exact Hi.
  - exact Ht.
Qed.

(*
│
│          A packed-channel hypothesis can be used directly to read
│          any in-horizon digit.
│
*)

(*              PacksChannel(B,H,x,X) ∧ t<H ⇒ Digit(B,X,t)=x(t)               *)

Lemma packs_channel_bound :
  forall B horizon xs X t,
    packs_channel B horizon xs X ->
    (t < horizon)%nat ->
    digit_at B X t = xs t.
Proof.
  intros B horizon xs X t Hpack Ht.
  exact (Hpack t Ht).
Qed.

(*
│
│          The canonical packed channel value satisfies the
│          packed-channel predicate when all digits are below the
│          base.
│
*)

(*         pow₂(B) ∧ ∀ i<H. x(i)<B ⇒ PacksChannel(B,H,x,Pack(B,H,x))          *)

Lemma pack_channel_value_packs :
  forall B horizon xs,
    pow2 B ->
    (forall i, (i < horizon)%nat -> xs i < B) ->
    packs_channel B horizon xs (pack_channel_value B horizon xs).
Proof.
  intros B horizon xs Hpow Hbound t Ht.
  apply pack_channel_value_digit; assumption.
Qed.

(*
│
│          The halt stream records halted states as digit `1` and
│          non-halted states as digit `0`.
│
*)

(*                           HaltDigit(code)∈{0,1}                            *)

Definition halt_digit_of_code (code : FMStateCode) : N :=
  if halted_code_b code then 1 else 0.

(*
│
│          Every halt digit is below two.
│
*)

(*                             HaltDigit(code)<2                              *)

Lemma halt_digit_of_code_bound :
  forall code,
    halt_digit_of_code code < 2.
Proof.
  intro code.
  unfold halt_digit_of_code.
  destruct (halted_code_b code); lia.
Qed.

(*
│
│          The state stream stores the raw encoded state code at each
│          time.
│
*)

(*                          StateStream(tr,t)=tr(t)                           *)

Definition trace_state_stream (tr : nat -> FMStateCode) (t : nat) : N :=
  N.of_nat (tr t).

(*
│
│          The instruction-pointer stream projects the current
│          instruction pointer from each encoded state.
│
*)

(*                     IpStream(tr,t)=ip(current(tr(t)))                      *)

Definition trace_ip_stream (tr : nat -> FMStateCode) (t : nat) : N :=
  N.of_nat (state_ip (current_state (tr t))).

(*
│
│          The first register stream projects register one from each
│          encoded state.
│
*)

(*                     R₁Stream(tr,t)=r₁(current(tr(t)))                      *)

Definition trace_r1_stream (tr : nat -> FMStateCode) (t : nat) : N :=
  N.of_nat (state_r1 (current_state (tr t))).

(*
│
│          The second register stream projects register two from each
│          encoded state.
│
*)

(*                     R₂Stream(tr,t)=r₂(current(tr(t)))                      *)

Definition trace_r2_stream (tr : nat -> FMStateCode) (t : nat) : N :=
  N.of_nat (state_r2 (current_state (tr t))).

(*
│
│          The halt stream projects the halt digit from each encoded
│          state.
│
*)

(*                     HaltStream(tr,t)=HaltDigit(tr(t))                      *)

Definition trace_halt_stream (tr : nat -> FMStateCode) (t : nat) : N :=
  halt_digit_of_code (tr t).

(*
│
│          A packed state view is the five decoded channel digits at
│          one time.
│
*)

(*                         View=(state,ip,r₁,r₂,halt)                         *)

Record packed_state_view : Type := {
  ps_state : N;
  ps_ip : N;
  ps_r1 : N;
  ps_r2 : N;
  ps_halt : N
}.

(*
│
│          Decoding a packed state at time `t` extracts digit `t` from
│          each of the five channels.
│
*)

(*                 ViewAt(p,v,t)=Digitₜ(state,ip,r₁,r₂,halt)                  *)

Definition packed_state_at
    (p : packed_trace_params) (v : packed_trace_vars) (t : nat)
    : packed_state_view :=
  {|
    ps_state := digit_at (pt_base p) (pt_state_ch v) t;
    ps_ip := digit_at (pt_base p) (pt_ip_ch v) t;
    ps_r1 := digit_at (pt_base p) (pt_r1_ch v) t;
    ps_r2 := digit_at (pt_base p) (pt_r2_ch v) t;
    ps_halt := digit_at (pt_base p) (pt_halt_ch v) t
  |}.

(*
│
│          A packed view matches an encoded state when all five
│          decoded fields equal the corresponding encoded-state
│          projections.
│
*)

(*             ViewMatches(view,code) ⇔ fields(view)=fields(code)             *)

Definition state_view_matches_code
    (view : packed_state_view) (code : FMStateCode) : Prop :=
  ps_state view = N.of_nat code /\
  ps_ip view = N.of_nat (state_ip (current_state code)) /\
  ps_r1 view = N.of_nat (state_r1 (current_state code)) /\
  ps_r2 view = N.of_nat (state_r2 (current_state code)) /\
  ps_halt view = halt_digit_of_code code.

(*
│
│          A packed valuation matches a trace at time `t` when the
│          decoded packed view matches trace state `t`.
│
*)

(*              PacksAt(p,v,tr,t) ⇔ ViewAt(p,v,t) matches tr(t)               *)

Definition packs_state_at
    (p : packed_trace_params) (v : packed_trace_vars)
    (tr : nat -> FMStateCode) (t : nat) : Prop :=
  state_view_matches_code (packed_state_at p v t) (tr t).

(*
│
│          A packed valuation packs a trace when it matches the trace
│          at every time below the horizon.
│
*)

(*               PacksTrace(p,v,tr) ⇔ ∀ t<H. PacksAt(p,v,tr,t)                *)

Definition packs_trace
    (p : packed_trace_params) (v : packed_trace_vars)
    (tr : nat -> FMStateCode) : Prop :=
  forall t, (t < pt_horizon p)%nat -> packs_state_at p v tr t.

(*
│
│          The packed-trace predicate is equivalent to five
│          independent channel-packing predicates.
│
*)

(*     PacksTrace ⇔ PacksState ∧ PacksIp ∧ PacksR₁ ∧ PacksR₂ ∧ PacksHalt      *)

Lemma packs_trace_iff_channels :
  forall p v tr,
    packs_trace p v tr <->
    packs_channel (pt_base p) (pt_horizon p) (trace_state_stream tr) (pt_state_ch v) /\
    packs_channel (pt_base p) (pt_horizon p) (trace_ip_stream tr) (pt_ip_ch v) /\
    packs_channel (pt_base p) (pt_horizon p) (trace_r1_stream tr) (pt_r1_ch v) /\
    packs_channel (pt_base p) (pt_horizon p) (trace_r2_stream tr) (pt_r2_ch v) /\
    packs_channel (pt_base p) (pt_horizon p) (trace_halt_stream tr) (pt_halt_ch v).
Proof.
  intros p v tr.
  split.
  - intro Hpack.
    repeat split; intros t Ht.
    + specialize (Hpack t Ht).
      unfold packs_state_at, state_view_matches_code, packed_state_at in Hpack.
      exact (proj1 Hpack).
    + specialize (Hpack t Ht).
      unfold packs_state_at, state_view_matches_code, packed_state_at in Hpack.
      exact (proj1 (proj2 Hpack)).
    + specialize (Hpack t Ht).
      unfold packs_state_at, state_view_matches_code, packed_state_at in Hpack.
      exact (proj1 (proj2 (proj2 Hpack))).
    + specialize (Hpack t Ht).
      unfold packs_state_at, state_view_matches_code, packed_state_at in Hpack.
      exact (proj1 (proj2 (proj2 (proj2 Hpack)))).
    + specialize (Hpack t Ht).
      unfold packs_state_at, state_view_matches_code, packed_state_at in Hpack.
      exact (proj2 (proj2 (proj2 (proj2 Hpack)))).
  - intros (Hstate & Hip & Hr1 & Hr2 & Hhalt) t Ht.
    unfold packs_state_at, state_view_matches_code, packed_state_at.
    repeat split.
    + apply Hstate.
      exact Ht.
    + apply Hip.
      exact Ht.
    + apply Hr1.
      exact Ht.
    + apply Hr2.
      exact Ht.
    + apply Hhalt.
      exact Ht.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                          PACKED CARRYLESS MASKS                         ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          Packed channel bounds assign a separate per-digit bound to
│          each semantic channel.
│
*)

(*                     Bounds=(stateB,ipB,r₁B,r₂B,haltB)                      *)

Record packed_channel_bounds : Type := {
  pcb_state_bound : N;
  pcb_ip_bound : N;
  pcb_r1_bound : N;
  pcb_r2_bound : N;
  pcb_halt_bound : N
}.

(*
│
│          Uniform channel bounds use the same digit bound for all
│          five channels.
│
*)

(*                        UniformBound(b)=(b,b,b,b,b)                         *)

Definition uniform_channel_bounds (b : N) : packed_channel_bounds :=
  {|
    pcb_state_bound := b;
    pcb_ip_bound := b;
    pcb_r1_bound := b;
    pcb_r2_bound := b;
    pcb_halt_bound := b
  |}.

(*
│
│          A single channel is digit-bounded when every in-horizon
│          digit is below the supplied bound.
│
*)

(*               ChannelBounded(p,b,X) ⇔ ∀ t<H. Digit(B,X,t)<b                *)

Definition channel_digits_bounded
    (p : packed_trace_params) (bound X : N) : Prop :=
  forall t, (t < pt_horizon p)%nat ->
    digit_at (pt_base p) X t < bound.

(*
│
│          Packed digit-boundedness requires the corresponding
│          digit-bound predicate for all five channels.
│
*)

(*    PackedBounded ⇔ BoundState ∧ BoundIp ∧ BoundR₁ ∧ BoundR₂ ∧ BoundHalt    *)

Definition packed_digits_bounded
    (p : packed_trace_params)
    (b : packed_channel_bounds)
    (v : packed_trace_vars) : Prop :=
  channel_digits_bounded p (pcb_state_bound b) (pt_state_ch v) /\
  channel_digits_bounded p (pcb_ip_bound b) (pt_ip_ch v) /\
  channel_digits_bounded p (pcb_r1_bound b) (pt_r1_ch v) /\
  channel_digits_bounded p (pcb_r2_bound b) (pt_r2_ch v) /\
  channel_digits_bounded p (pcb_halt_bound b) (pt_halt_ch v).

(*
│
│          The mask digit for a bound is the complement interval
│          between the bound and the base.
│
*)

(*                             MaskDigit(B,b)=B−b                             *)

Definition bound_mask_digit (B bound : N) : N :=
  B - bound.

(*
│
│          A bound mask channel repeats the same complement-mask digit
│          through the horizon.
│
*)

(*                     MaskValue(B,H,b)=Pack(B,H,λx. B−b)                     *)

Definition bound_mask_value
    (B : N) (horizon : nat) (bound : N) : N :=
  pack_channel_value B horizon (fun _ => bound_mask_digit B bound).

(*
│
│          A channel satisfies its mask constraint when the channel
│          value is carryless from the repeated bound mask.
│
*)

(*           MaskConstraint(p,b,X) ⇔ carryless₂(X,MaskValue(B,H,b))           *)

Definition channel_mask_constraint
    (p : packed_trace_params) (bound X : N) : Prop :=
  carryless2 X (bound_mask_value (pt_base p) (pt_horizon p) bound).

(*
│
│          Packed mask constraints require the corresponding carryless
│          mask constraint for all five channels.
│
*)

(*       PackedMasks ⇔ MaskState ∧ MaskIp ∧ MaskR₁ ∧ MaskR₂ ∧ MaskHalt        *)

Definition packed_mask_constraints
    (p : packed_trace_params)
    (b : packed_channel_bounds)
    (v : packed_trace_vars) : Prop :=
  channel_mask_constraint p (pcb_state_bound b) (pt_state_ch v) /\
  channel_mask_constraint p (pcb_ip_bound b) (pt_ip_ch v) /\
  channel_mask_constraint p (pcb_r1_bound b) (pt_r1_ch v) /\
  channel_mask_constraint p (pcb_r2_bound b) (pt_r2_ch v) /\
  channel_mask_constraint p (pcb_halt_bound b) (pt_halt_ch v).

(*
│
│          Channel-bound well-formedness requires every bound to be a
│          binary power strictly below the packed base.
│
*)

(*         BoundsWF(p,b) ⇔ ∀ c∈Channels. pow₂(bound(c)) ∧ bound(c)<B          *)

Definition channel_bounds_wf
    (p : packed_trace_params) (b : packed_channel_bounds) : Prop :=
  pow2 (pcb_state_bound b) /\ pcb_state_bound b < pt_base p /\
  pow2 (pcb_ip_bound b) /\ pcb_ip_bound b < pt_base p /\
  pow2 (pcb_r1_bound b) /\ pcb_r1_bound b < pt_base p /\
  pow2 (pcb_r2_bound b) /\ pcb_r2_bound b < pt_base p /\
  pow2 (pcb_halt_bound b) /\ pcb_halt_bound b < pt_base p.

(*
│
│          Every binary power is strictly positive.
│
*)

(*                               pow₂(B) ⇒ 0<B                                *)

Lemma pow2_positive :
  forall B,
    pow2 B ->
    0 < B.
Proof.
  intros B [k ->].
  pose proof (pow2_lower_bound k).
  lia.
Qed.

(*
│
│          Carrylessness is symmetric.
│
*)

(*                     carryless₂(S,T) ⇒ carryless₂(T,S)                      *)

Lemma carryless2_sym :
  forall S T,
    carryless2 S T ->
    carryless2 T S.
Proof.
  intros S T Hcarry.
  unfold carryless2 in *.
  rewrite N.land_comm.
  exact Hcarry.
Qed.

(*
│
│          A constant stream is independent of the start offset used
│          by recursive packing.
│
*)

(*                PackFrom(B,s₁,H,λx.d)=PackFrom(B,s₂,H,λx.d)                 *)

Lemma pack_channel_value_from_const :
  forall B start1 start2 horizon d,
    pack_channel_value_from B start1 horizon (fun _ => d) =
    pack_channel_value_from B start2 horizon (fun _ => d).
Proof.
  intros B start1 start2 horizon d.
  revert start1 start2.
  induction horizon as [|h IH]; intros start1 start2; simpl.
  - reflexivity.
  - rewrite (IH (S start1) (S start2)).
    reflexivity.
Qed.

(*
│
│          A nonempty bound-mask value unfolds into one mask digit
│          plus the shifted tail mask.
│
*)

(*            MaskValue(B,S H,b)=MaskDigit(B,b)+B·MaskValue(B,H,b)            *)

Lemma bound_mask_value_unfold :
  forall B horizon bound,
    bound_mask_value B (S horizon) bound =
    bound_mask_digit B bound + B * bound_mask_value B horizon bound.
Proof.
  intros B horizon bound.
  unfold bound_mask_value, pack_channel_value, bound_mask_digit.
  simpl.
  rewrite (pack_channel_value_from_const B 1 0 horizon (B - bound)).
  reflexivity.
Qed.

(*
│
│          The zeroth digit is the value modulo the base.
│
*)

(*                            Digit(B,X,0)=X mod B                            *)

Lemma digit_at_zero :
  forall B X,
    digit_at B X 0 = X mod B.
Proof.
  intros B X.
  unfold digit_at.
  rewrite base_pow_0.
  rewrite N.div_1_r.
  reflexivity.
Qed.

(*
│
│          Every extracted digit is below the base when the base is a
│          nonzero binary power.
│
*)

(*                          pow₂(B) ⇒ Digit(B,X,t)<B                          *)

Lemma digit_at_lt_base :
  forall B X t,
    pow2 B ->
    digit_at B X t < B.
Proof.
  intros B X t Hpow.
  unfold digit_at.
  apply N.mod_upper_bound.
  now apply pow2_nonzero.
Qed.

(*
│
│          Dividing the whole channel by the base shifts digit
│          extraction by one position.
│
*)

(*                      Digit(B,⌊X÷B⌋,t)=Digit(B,X,S t)                       *)

Lemma digit_at_div_base :
  forall B X t,
    pow2 B ->
    digit_at B (X / B) t = digit_at B X (S t).
Proof.
  intros B X t Hpow.
  unfold digit_at.
  rewrite base_pow_succ.
  rewrite <- (N.Div0.div_div X B (base_pow B t)).
  reflexivity.
Qed.

(*
│
│          A channel decomposes into its lowest digit plus the
│          base-shifted quotient tail.
│
*)

(*                           X=Digit(B,X,0)+B·⌊X÷B⌋                           *)

Lemma digit_at_decompose :
  forall B X,
    pow2 B ->
    X = digit_at B X 0 + B * (X / B).
Proof.
  intros B X Hpow.
  rewrite digit_at_zero.
  rewrite N.add_comm.
  apply N.div_mod.
  now apply pow2_nonzero.
Qed.

(*
│
│          A complement mask digit is itself below the base when the
│          bound is a positive binary power below the base.
│
*)

(*                           pow₂(b) ∧ b<B ⇒ B−b<B                            *)

Lemma bound_mask_digit_lt_base :
  forall B bound,
    pow2 bound ->
    bound < B ->
    bound_mask_digit B bound < B.
Proof.
  intros B bound Hpow Hlt.
  unfold bound_mask_digit.
  pose proof (pow2_positive bound Hpow).
  lia.
Qed.

(*
│
│          A carryless stacked pair can be unstacked into
│          carrylessness of its low and high parts.
│
*)

(*   carryless₂(S₁+S₂·2ⁿ,T₁+T₂·2ⁿ) ⇒ carryless₂(S₁,T₁) ∧ carryless₂(S₂,T₂)    *)

Lemma carryless_unstack_pow2 :
  forall n S1 T1 S2 T2,
    S1 < 2 ^ n ->
    T1 < 2 ^ n ->
    carryless2 (S1 + S2 * 2 ^ n) (T1 + T2 * 2 ^ n) ->
    carryless2 S1 T1 /\ carryless2 S2 T2.
Proof.
  intros n S1 T1 S2 T2 HS1 HT1 Hcarry.
  split.
  - unfold carryless2.
    apply N.bits_inj_0.
    intro m.
    rewrite N.land_spec.
    destruct (N.lt_ge_cases m n) as [Hmn|Hmn].
    + assert
        (Hbit :
          N.testbit
            (N.land (S1 + S2 * 2 ^ n) (T1 + T2 * 2 ^ n)) m = false).
      {
        rewrite Hcarry.
        apply N.bits_0.
      }
      rewrite N.land_spec in Hbit.
      rewrite (add_shift_testbit_low S1 S2 n m HS1 Hmn) in Hbit.
      rewrite (add_shift_testbit_low T1 T2 n m HT1 Hmn) in Hbit.
      exact Hbit.
    + rewrite (lt_pow2_bits_false S1 n m HS1 Hmn).
      rewrite (lt_pow2_bits_false T1 n m HT1 Hmn).
      reflexivity.
  - unfold carryless2.
    apply N.bits_inj_0.
    intro m.
    rewrite N.land_spec.
    assert
      (Hbit :
        N.testbit
          (N.land (S1 + S2 * 2 ^ n) (T1 + T2 * 2 ^ n)) (m + n) = false).
    {
      rewrite Hcarry.
      apply N.bits_0.
    }
    rewrite N.land_spec in Hbit.
    rewrite (add_shift_testbit_high S1 S2 n (m + n) HS1) in Hbit by lia.
    rewrite (add_shift_testbit_high T1 T2 n (m + n) HT1) in Hbit by lia.
    replace (m + n - n) with m in Hbit by lia.
    exact Hbit.
Qed.

(*
│
│          The unstacking law also holds when the split base is
│          supplied abstractly as a binary power.
│
*)

(*    carryless₂(S₁+S₂·N,T₁+T₂·N) ⇒ carryless₂(S₁,T₁) ∧ carryless₂(S₂,T₂)     *)

Lemma carryless_unstack_2 :
  forall N S1 T1 S2 T2,
    pow2 N ->
    S1 < N ->
    T1 < N ->
    carryless2 (S1 + S2 * N) (T1 + T2 * N) ->
    carryless2 S1 T1 /\ carryless2 S2 T2.
Proof.
  intros N S1 T1 S2 T2 [n ->] HS1 HT1 Hcarry.
  eapply carryless_unstack_pow2; eassumption.
Qed.

(*
│
│          The repeated bound mask is correct: being carryless from it
│          is exactly digitwise boundedness below the supplied bound.
│
*)

(*           carryless₂(X,MaskValue(B,H,b)) ⇔ ∀ t<H. Digit(B,X,t)<b           *)

Lemma bound_mask_value_correct :
  forall B horizon bound X,
    pow2 B ->
    pow2 bound ->
    bound < B ->
    carryless2 X (bound_mask_value B horizon bound) <->
    forall t, (t < horizon)%nat -> digit_at B X t < bound.
Proof.
  intros B horizon.
  induction horizon as [|h IH]; intros bound X HpowB HpowBound Hlt.
  - split.
    + intros _ t Ht.
      lia.
    + intro Htrivial.
      unfold carryless2, bound_mask_value, pack_channel_value.
      simpl.
      rewrite N.land_0_r.
      reflexivity.
  - split.
    + intro Hcarry.
      pose proof
        (carryless_unstack_2
           B
           (digit_at B X 0)
           (bound_mask_digit B bound)
           (X / B)
           (bound_mask_value B h bound)
           HpowB
           (digit_at_lt_base B X 0 HpowB)
           (bound_mask_digit_lt_base B bound HpowBound Hlt)) as Hunstack.
      rewrite (digit_at_decompose B X HpowB) in Hcarry.
      rewrite (bound_mask_value_unfold B h bound) in Hcarry.
      rewrite (N.mul_comm B (X / B)) in Hcarry.
      rewrite (N.mul_comm B (bound_mask_value B h bound)) in Hcarry.
      specialize (Hunstack Hcarry).
      destruct Hunstack as [Hlow Hhigh].
      intros t Ht.
      destruct t as [|t'].
      * apply
          (proj2
             (carryless_bound_iff
                B bound (digit_at B X 0)
                HpowB HpowBound Hlt (digit_at_lt_base B X 0 HpowB))).
        apply carryless2_sym.
        exact Hlow.
      * rewrite <- (digit_at_div_base B X t' HpowB).
        pose proof
          (proj1 (IH bound (X / B) HpowB HpowBound Hlt) Hhigh) as Htail.
        apply Htail.
        lia.
    + intro Hdigits.
      rewrite (digit_at_decompose B X HpowB).
      rewrite (bound_mask_value_unfold B h bound).
      rewrite (N.mul_comm B (X / B)).
      rewrite (N.mul_comm B (bound_mask_value B h bound)).
      apply carryless_stack_2.
      * exact HpowB.
      * apply digit_at_lt_base.
        exact HpowB.
      * apply bound_mask_digit_lt_base.
        -- exact HpowBound.
        -- exact Hlt.
      * apply carryless2_sym.
        apply
          (proj1
             (carryless_bound_iff
                B bound (digit_at B X 0)
                HpowB HpowBound Hlt (digit_at_lt_base B X 0 HpowB))).
        apply Hdigits.
        lia.
      * apply (proj2 (IH bound (X / B) HpowB HpowBound Hlt)).
        intros t Ht.
        rewrite digit_at_div_base by exact HpowB.
        apply Hdigits.
        lia.
Qed.

(*
│
│          Every channel is digit-bounded by the packed base itself.
│
*)

(*                        ChannelBounded(p,base(p),X)                         *)

Lemma channel_digits_bounded_base :
  forall p X,
    channel_digits_bounded p (pt_base p) X.
Proof.
  intros p X t Ht.
  apply digit_at_lt_base.
  exact (pt_base_pow2 p).
Qed.

(*
│
│          For one channel, the carryless mask constraint is
│          equivalent to digitwise boundedness under a well-formed
│          power-of-two bound.
│
*)

(*       pow₂(b) ∧ b<B ⇒ MaskConstraint(p,b,X) ⇔ ChannelBounded(p,b,X)        *)

Lemma channel_mask_constraint_correct :
  forall p bound X,
    pow2 bound ->
    bound < pt_base p ->
    channel_mask_constraint p bound X <->
    channel_digits_bounded p bound X.
Proof.
  intros p bound X HpowBound Hlt.
  unfold channel_mask_constraint, channel_digits_bounded.
  apply bound_mask_value_correct.
  - exact (pt_base_pow2 p).
  - exact HpowBound.
  - exact Hlt.
Qed.

(*
│
│          For all five channels, packed mask constraints are
│          equivalent to packed digit-boundedness under well-formed
│          bounds.
│
*)

(*         BoundsWF(p,b) ⇒ PackedMasks(p,b,v) ⇔ PackedBounded(p,b,v)          *)

Lemma packed_mask_constraints_correct :
  forall p b v,
    channel_bounds_wf p b ->
    packed_mask_constraints p b v <->
    packed_digits_bounded p b v.
Proof.
  intros p b v
    (HstatePow & HstateLt &
     HipPow & HipLt &
     Hr1Pow & Hr1Lt &
     Hr2Pow & Hr2Lt &
     HhaltPow & HhaltLt).
  unfold packed_mask_constraints, packed_digits_bounded.
  split.
  - intros (Hstate & Hip & Hr1 & Hr2 & Hhalt).
    repeat split.
    + apply (proj1 (channel_mask_constraint_correct
                      p (pcb_state_bound b) (pt_state_ch v)
                      HstatePow HstateLt)).
      exact Hstate.
    + apply (proj1 (channel_mask_constraint_correct
                      p (pcb_ip_bound b) (pt_ip_ch v)
                      HipPow HipLt)).
      exact Hip.
    + apply (proj1 (channel_mask_constraint_correct
                      p (pcb_r1_bound b) (pt_r1_ch v)
                      Hr1Pow Hr1Lt)).
      exact Hr1.
    + apply (proj1 (channel_mask_constraint_correct
                      p (pcb_r2_bound b) (pt_r2_ch v)
                      Hr2Pow Hr2Lt)).
      exact Hr2.
    + apply (proj1 (channel_mask_constraint_correct
                      p (pcb_halt_bound b) (pt_halt_ch v)
                      HhaltPow HhaltLt)).
      exact Hhalt.
  - intros (Hstate & Hip & Hr1 & Hr2 & Hhalt).
    repeat split.
    + apply (proj2 (channel_mask_constraint_correct
                      p (pcb_state_bound b) (pt_state_ch v)
                      HstatePow HstateLt)).
      exact Hstate.
    + apply (proj2 (channel_mask_constraint_correct
                      p (pcb_ip_bound b) (pt_ip_ch v)
                      HipPow HipLt)).
      exact Hip.
    + apply (proj2 (channel_mask_constraint_correct
                      p (pcb_r1_bound b) (pt_r1_ch v)
                      Hr1Pow Hr1Lt)).
      exact Hr1.
    + apply (proj2 (channel_mask_constraint_correct
                      p (pcb_r2_bound b) (pt_r2_ch v)
                      Hr2Pow Hr2Lt)).
      exact Hr2.
    + apply (proj2 (channel_mask_constraint_correct
                      p (pcb_halt_bound b) (pt_halt_ch v)
                      HhaltPow HhaltLt)).
      exact Hhalt.
Qed.

(*
│
│          A packed trace with valid mask constraints has bounded
│          packed digits.
│
*)

(*            PacksTrace ∧ PackedMasks ∧ BoundsWF ⇒ PackedBounded             *)

Lemma packs_trace_masked_digits_bounded :
  forall p bounds v tr,
    packs_trace p v tr ->
    packed_mask_constraints p bounds v ->
    channel_bounds_wf p bounds ->
    packed_digits_bounded p bounds v.
Proof.
  intros p bounds v tr Hpacks Hmask Hwf.
  apply (proj1 (packed_mask_constraints_correct p bounds v Hwf)).
  exact Hmask.
Qed.
