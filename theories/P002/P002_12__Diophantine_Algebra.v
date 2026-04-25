(*P002_12__Diophantine_Algebra.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                   Proofcase / P002_12__Diophantine_Algebra                   │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file packages the algebraic backbone of the Diophantine route. It
  proves exact two-adic multiplication and quotient laws, the Legendre
  valuation v₂(n!) = n - s₂(n), and assembles the packed-mask Diophantine
  instance that consumes those facts.

*)

(*
│
│          This algebra package uses binary naturals and linear
│          arithmetic for exact two-adic and packed-mask bounds.
│
*)

(*                                  ℕ₂ ∧ lia                                  *)

From Stdlib Require Import NArith Lia.

(*
│
│          This file consumes the binomial two-adic core, exports the
│          carryless bitcount bridge, and uses local packed semantics
│          for the stacked mask instance.
│
*)

(*                     P002₁₀ ∧ P002₁₁ ∧ P002₀₈ → P002₁₂                      *)

From P002 Require Import P002_10__Binomial_TwoAdic_Core.
From P002 Require Export P002_11__Carryless_Bitcount_Bridge.
From P002 Require Import P002_08__Packed_Local_Semantics.

Module CC := P002_07__Packed_Carryless_Masks.
Module PMS := P002_08__Packed_Local_Semantics.

Local Notation pow2 := CC.pow2.
Local Notation stacked_mask_instance := PMS.stacked_mask_instance.
Local Notation mask_stack_wf := PMS.mask_stack_wf.
Local Notation packed_mask_stack_constraint := PMS.packed_mask_stack_constraint.

Local Open Scope N_scope.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                          EXACT TWO-ADIC ALGEBRA                         ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        EXACT ORDER FACTORIZATION                        ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          An exact two-adic order gives the canonical shape: a power
│          of two times an odd residual.
│
*)

(*                     Exact(n,e) ⇒ ∃ o. n=2ᵉ·o ∧ Odd(o)                      *)

Lemma two_adic_exact_factor_odd :
  forall n e,
    two_adic_exact n e ->
    exists o,
      n = 2 ^ e * o /\
      N.odd o = true.
Proof.
  intros n e Hexact.
  destruct (proj2 (Hexact e) ltac:(lia)) as [o Ho].
  exists o.
  split.
  - exact Ho.
  - destruct (N.Even_or_Odd o) as [[o' HoEven]|HoOdd].
    + exfalso.
      assert (Htoo_many : two_adic_order_ge n (N.succ e)).
      {
        unfold two_adic_order_ge.
        exists o'.
        rewrite Ho.
        rewrite HoEven.
        rewrite N.pow_succ_r by lia.
        nia.
      }
      pose proof (proj1 (Hexact (N.succ e)) Htoo_many) as Hle.
      lia.
    + apply N.odd_spec.
      exact HoOdd.
Qed.

(*
│
│          Any value with an exact two-adic order is nonzero.
│
*)

(*                              Exact(n,e) ⇒ n≠0                              *)

Lemma two_adic_exact_nonzero :
  forall n e,
    two_adic_exact n e ->
    n <> 0.
Proof.
  intros n e Hexact Hzero.
  subst n.
  pose proof (proj1 (Hexact (N.succ e)) (two_adic_order_ge_zero_value _)) as Hle.
  lia.
Qed.

(*
│
│          An odd right factor can be cancelled from an exact two-adic
│          order.
│
*)

(*                     Odd(o) ∧ Exact(n·o,e) ⇒ Exact(n,e)                     *)

Lemma two_adic_exact_cancel_odd_r :
  forall n o e,
    N.odd o = true ->
    two_adic_exact (n * o) e ->
    two_adic_exact n e.
Proof.
  unfold two_adic_exact.
  intros n o e Hodd Hexact m.
  split.
  - intro Hge.
    apply Hexact.
    replace m with (m + 0) by lia.
    apply two_adic_order_ge_mul.
    + exact Hge.
    + apply two_adic_order_ge_zero_exponent.
  - intro Hle.
    apply (two_adic_order_ge_mul_odd_cancel_r n o m).
    + exact Hodd.
    + apply Hexact.
      exact Hle.
Qed.

(*
│
│          An odd left factor can be cancelled from an exact two-adic
│          order.
│
*)

(*                     Odd(o) ∧ Exact(o·n,e) ⇒ Exact(n,e)                     *)

Lemma two_adic_exact_cancel_odd_l :
  forall o n e,
    N.odd o = true ->
    two_adic_exact (o * n) e ->
    two_adic_exact n e.
Proof.
  intros o n e Hodd Hexact.
  rewrite N.mul_comm in Hexact.
  apply (two_adic_exact_cancel_odd_r n o e); assumption.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                              MULTIPLICATION                             ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          Exact two-adic orders add under multiplication.
│
*)

(*                Exact(a,eₐ) ∧ Exact(b,eᵦ) ⇒ Exact(a·b,eₐ+eᵦ)                *)

Theorem two_adic_exact_mul_adds_proved :
  two_adic_exact_mul_adds.
Proof.
  unfold two_adic_exact_mul_adds.
  intros a b ea eb Ha Hb.
  destruct (two_adic_exact_factor_odd a ea Ha) as [oa [Ha_eq Hoa]].
  destruct (two_adic_exact_factor_odd b eb Hb) as [ob [Hb_eq Hob]].
  rewrite Ha_eq, Hb_eq.
  replace ((2 ^ ea * oa) * (2 ^ eb * ob))
    with (2 ^ (ea + eb) * (oa * ob)).
  - apply two_adic_exact_mul_odd_r.
    + rewrite N.odd_mul.
      rewrite Hoa, Hob.
      reflexivity.
    + apply two_adic_exact_pow2.
  - rewrite N.pow_add_r.
    nia.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                             EXACT QUOTIENTS                             ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          Exact two-adic orders subtract across an exact nonzero
│          quotient.
│
*)

(*      q·d=n ∧ d≠0 ∧ eᵈ≤eⁿ ∧ Exact(n,eⁿ) ∧ Exact(d,eᵈ) ⇒ Exact(q,eⁿ−eᵈ)      *)

Theorem two_adic_exact_quotient_subtracts_proved :
  two_adic_exact_quotient_subtracts.
Proof.
  unfold two_adic_exact_quotient_subtracts.
  intros n d q en ed Hqd _Hd_nonzero Hed_le Hn Hd.
  destruct (two_adic_exact_factor_odd n en Hn) as [on [Hn_eq Hon]].
  destruct (two_adic_exact_factor_odd d ed Hd) as [od [Hd_eq Hod]].
  assert (Hqod :
    q * od = 2 ^ (en - ed) * on).
  {
    rewrite Hn_eq in Hqd.
    rewrite Hd_eq in Hqd.
    replace (q * (2 ^ ed * od)) with (2 ^ ed * (q * od)) in Hqd by nia.
    replace (2 ^ en * on) with (2 ^ ed * (2 ^ (en - ed) * on)) in Hqd.
    - apply N.mul_reg_l with (p := 2 ^ ed).
      + pose proof (pow2_value_positive ed).
        lia.
      + exact Hqd.
    - replace (2 ^ ed * (2 ^ (en - ed) * on))
        with ((2 ^ ed * 2 ^ (en - ed)) * on) by nia.
      rewrite <- N.pow_add_r.
      replace (ed + (en - ed)) with en by lia.
      reflexivity.
  }
  apply (two_adic_exact_cancel_odd_r q od (en - ed)).
  - exact Hod.
  - rewrite Hqod.
    apply two_adic_exact_mul_odd_r.
    + exact Hon.
    + apply two_adic_exact_pow2.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                          BITCOUNT SUCCESSOR LAW                         ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          Successor increases full bitcount by at most one.
│
*)

(*                             Pop(S n)≤S(Pop(n))                             *)

Lemma full_bitcount_succ_le :
  forall n,
    full_bitcount (N.succ n) <= N.succ (full_bitcount n).
Proof.
  assert
    (Hsucc_double :
      forall n,
        full_bitcount (N.succ_double n) = N.succ (full_bitcount n)).
  {
    intro n.
    unfold full_bitcount at 1.
    assert
      (Hsize :
        N.size (N.succ_double n) = N.succ (N.size n)).
    {
      destruct (N.eq_dec n 0) as [->|Hn_nonzero].
      - reflexivity.
      - rewrite N.succ_double_spec.
        rewrite N.size_log2 by nia.
        rewrite N.log2_succ_double by lia.
        rewrite N.size_log2 by exact Hn_nonzero.
        reflexivity.
    }
    rewrite Hsize.
    rewrite N2Nat.inj_succ.
    rewrite bitcount_window_succ_div2.
    rewrite N.succ_double_spec.
    rewrite N.testbit_odd_0.
    rewrite <- N.div2_div.
    rewrite N.div2_odd'.
    unfold bit_value, full_bitcount.
    lia.
  }
  induction n using N.binary_ind.
  - change (N.succ 0) with 1.
    rewrite full_bitcount_0, full_bitcount_1.
    lia.
  - rewrite N.double_spec.
    replace (N.succ (2 * n)) with (N.succ_double n)
      by (rewrite N.succ_double_spec; lia).
    rewrite Hsucc_double.
    rewrite full_bitcount_double.
    lia.
  - rewrite N.succ_double_spec.
    replace (N.succ (2 * n + 1)) with (2 * N.succ n) by lia.
    rewrite full_bitcount_double.
    rewrite <- N.succ_double_spec.
    rewrite Hsucc_double.
    lia.
Qed.

(*
│
│          The bitcount deficit across successor equals the exact
│          two-adic order of the successor.
│
*)

(*                    Exact(S n,e) ⇒ Pop(S n)+e=S(Pop(n))                     *)

Lemma full_bitcount_succ_eq_valuation :
  forall n e,
    two_adic_exact (N.succ n) e ->
    full_bitcount (N.succ n) + e = N.succ (full_bitcount n).
Proof.
  assert
    (Hdiff :
      forall n,
        exists k,
          full_bitcount (N.succ n) + k =
            N.succ (full_bitcount n) /\
          two_adic_exact (N.succ n) k).
  {
    assert
      (Hsucc_double :
        forall n,
          full_bitcount (N.succ_double n) = N.succ (full_bitcount n)).
    {
      intro n.
      unfold full_bitcount at 1.
      assert
        (Hsize :
          N.size (N.succ_double n) = N.succ (N.size n)).
      {
        destruct (N.eq_dec n 0) as [->|Hn_nonzero].
        - reflexivity.
        - rewrite N.succ_double_spec.
          rewrite N.size_log2 by nia.
          rewrite N.log2_succ_double by lia.
          rewrite N.size_log2 by exact Hn_nonzero.
          reflexivity.
      }
      rewrite Hsize.
      rewrite N2Nat.inj_succ.
      rewrite bitcount_window_succ_div2.
      rewrite N.succ_double_spec.
      rewrite N.testbit_odd_0.
      rewrite <- N.div2_div.
      rewrite N.div2_odd'.
      unfold bit_value, full_bitcount.
      lia.
    }
    induction n using N.binary_ind.
    - exists 0.
      change (N.succ 0) with 1.
      rewrite full_bitcount_0, full_bitcount_1.
      split.
      + reflexivity.
      + change (N.succ 0) with 1.
        apply two_adic_exact_one.
    - exists 0.
      rewrite N.double_spec.
      replace (N.succ (2 * n)) with (N.succ_double n)
        by (rewrite N.succ_double_spec; lia).
      rewrite Hsucc_double.
      rewrite full_bitcount_double.
      split.
      + lia.
      + apply two_adic_exact_odd.
        rewrite N.succ_double_spec.
        apply N.odd_odd.
    - destruct IHn as [k [Hbits Hexact]].
      exists (N.succ k).
      rewrite N.succ_double_spec.
      replace (N.succ (2 * n + 1)) with (2 * N.succ n) by lia.
      rewrite full_bitcount_double.
      rewrite <- N.succ_double_spec.
      rewrite Hsucc_double.
      split.
      + lia.
      + apply two_adic_exact_double.
        exact Hexact.
  }
  intros n e Hexact.
  destruct (Hdiff n) as [k [Hbits Hk]].
  assert (Heq : e = k).
  {
    assert (He_le : e <= k).
    {
      apply Hk.
      apply Hexact.
      lia.
    }
    assert (Hk_le : k <= e).
    {
      apply Hexact.
      apply Hk.
      lia.
    }
    lia.
  }
  subst e.
  exact Hbits.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                         SUCCESSOR TWO-ADIC DELTA                        ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The increment of `n−Pop(n)` from `n` to `S n` is the exact
│          two-adic order of `S n`.
│
*)

(*                  Exact(S n,e) ⇒ S n−Pop(S n)=(n−Pop(n))+e                  *)

Lemma successor_two_adic_exact_delta :
  forall n e,
    two_adic_exact (N.succ n) e ->
    N.succ n - full_bitcount (N.succ n) =
      (n - full_bitcount n) + e.
Proof.
  intros n e Hexact.
  pose proof (full_bitcount_succ_eq_valuation n e Hexact) as Hbits.
  pose proof (full_bitcount_le_self n) as Hle_n.
  pose proof (full_bitcount_le_self (N.succ n)) as Hle_succ.
  lia.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                           FACTORIAL VALUATION                           ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          One factorial successor step preserves Legendre's exact
│          exponent formula.
│
*)

(*          Exact(Fact(n),n−Pop(n)) ⇒ Exact(Fact(S n),S n−Pop(S n))           *)

Lemma factorial_two_adic_exponent_step :
  forall n,
    two_adic_exact (factorialN n) (n - full_bitcount n) ->
    two_adic_exact
      (factorialN (N.succ n))
      (N.succ n - full_bitcount (N.succ n)).
Proof.
  assert
    (Hsucc_exact :
      forall n,
        exists e,
          two_adic_exact (N.succ n) e).
  {
    induction n using N.binary_ind.
    - exists 0.
      change (N.succ 0) with 1.
      apply two_adic_exact_one.
    - exists 0.
      rewrite N.double_spec.
      replace (N.succ (2 * n)) with (N.succ_double n)
        by (rewrite N.succ_double_spec; lia).
      apply two_adic_exact_odd.
      rewrite N.succ_double_spec.
      apply N.odd_odd.
    - destruct IHn as [e Hexact].
      exists (N.succ e).
      rewrite N.succ_double_spec.
      replace (N.succ (2 * n + 1)) with (2 * N.succ n) by lia.
      apply two_adic_exact_double.
      exact Hexact.
  }
  intros n Hfactorial.
  destruct (Hsucc_exact n) as [e Hexact_succ].
  destruct (two_adic_exact_factor_odd (N.succ n) e Hexact_succ)
    as [_odd [_Hfactor _Hodd]].
  rewrite factorialN_succ.
  replace
    (N.succ n - full_bitcount (N.succ n))
    with ((n - full_bitcount n) + e)
    by (symmetry; apply successor_two_adic_exact_delta; exact Hexact_succ).
  rewrite N.mul_comm.
  apply two_adic_exact_mul_adds_proved.
  - exact Hfactorial.
  - exact Hexact_succ.
Qed.

(*
│
│          Legendre's base-two factorial valuation formula is closed
│          in exact two-adic form.
│
*)

(*                          Exact(Fact(n),n−Pop(n))                           *)

Theorem factorial_two_adic_exact_proved :
  factorial_two_adic_exact.
Proof.
  unfold factorial_two_adic_exact.
  induction n using N.peano_ind.
  - replace (0 - full_bitcount 0) with 0
      by (rewrite full_bitcount_0; lia).
    rewrite factorialN_0.
    apply two_adic_exact_one.
  - apply factorial_two_adic_exponent_step.
    exact IHn.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                      CENTRAL BINOMIAL ROUTE WIRING                      ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The conditional wrapper exposes the central-binomial
│          factorial two-adic bridge from any proof of factorial
│          exactness.
│
*)

(*                        Legendre ⇒ CentralFactBridge                        *)

Theorem central_binomial_factorial_two_adic_bridge_from_factorial_exact :
  factorial_two_adic_exact ->
  central_binomial_factorial_two_adic_bridge.
Proof.
  intro Hfactorial.
  apply central_binomial_factorial_two_adic_bridge_from_exact_route.
  - exact Hfactorial.
  - exact two_adic_exact_mul_adds_proved.
  - exact two_adic_exact_quotient_subtracts_proved.
Qed.

(*
│
│          The central-binomial factorial two-adic bridge is closed
│          using the factorial valuation proved above.
│
*)

(*                             CentralFactBridge                              *)

Theorem central_binomial_factorial_two_adic_bridge_proved :
  central_binomial_factorial_two_adic_bridge.
Proof.
  exact
    (central_binomial_factorial_two_adic_bridge_from_factorial_exact
       factorial_two_adic_exact_proved).
Qed.

(*
│
│          The public central-binomial bitcount bridge is closed by
│          combining the factorial value bridge and the factorial
│          two-adic bridge.
│
*)

(*                          2ᵐ∣Central(r) ⇔ m≤Pop(r)                          *)

Theorem central_binomial_bitcount_bridge_proved :
  central_binomial_bitcount_bridge.
Proof.
  apply central_binomial_bitcount_bridge_from_factorial_route.
  - exact central_binomial_factorial_bridge_proved.
  - exact central_binomial_factorial_two_adic_bridge_proved.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        CARRYLESS BINOMIAL BRIDGE                        ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The carryless binomial bridge is closed by combining the
│          central-binomial bitcount bridge with the local threshold
│          theorem from P002₁₁.
│
*)

(*                          CarrylessBinomialBridge                           *)

Theorem carryless_binomial_bridge_proved :
  carryless_binomial_bridge.
Proof.
  apply carryless_binomial_bridge_from_bitcount_bridges.
  - exact central_binomial_bitcount_bridge_proved.
  - exact carryless_bridge_R_bitcount_threshold_proved.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                       PACKED DIOPHANTINE INSTANCE                       ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The packed-mask bridge base is the fifth power of the stack
│          base, matching the five stacked channels.
│
*)

(*                       BridgeBase(sm)=stackBase(sm)⁵                        *)

Definition packed_mask_bridge_base (sm : stacked_mask_instance) : N :=
  let B := PMS.sm_stack_base sm in
  B * B * B * B * B.

(*
│
│          The carryless Diophantine instance stores the bridge base,
│          source, target, modulus, bridge argument, and central
│          binomial value.
│
*)

(*                      Instance=(B,S,T,M,R,Central(R))                       *)

Record carryless_diophantine_instance : Type := {
  cdi_bridge_base : N;
  cdi_source : N;
  cdi_target : N;
  cdi_modulus : N;
  cdi_bridge_R : N;
  cdi_central_binomial : N
}.

(*
│
│          Instance well-formedness says the carryless-binomial data
│          are well formed and the stored fields are coherent.
│
*)

(*      InstanceWF ⇔ WF(B,S,T) ∧ M=B² ∧ R=BridgeR(B,S,T) ∧ C=Central(R)       *)

Definition carryless_diophantine_wf
    (inst : carryless_diophantine_instance) : Prop :=
  carryless_binomial_wf
    (cdi_bridge_base inst) (cdi_source inst) (cdi_target inst) /\
  cdi_modulus inst = carryless_square_modulus (cdi_bridge_base inst) /\
  cdi_bridge_R inst =
    carryless_bridge_R
      (cdi_bridge_base inst) (cdi_source inst) (cdi_target inst) /\
  cdi_central_binomial inst = central_binomial (cdi_bridge_R inst).

(*
│
│          The packed-mask compiler maps a stacked mask instance to
│          its carryless Diophantine instance.
│
*)

(*     Compile(sm)=(BridgeBase,S,T,BridgeBase²,BridgeR,Central(BridgeR))      *)

Definition packed_mask_diophantine_instance_of
    (sm : stacked_mask_instance) : carryless_diophantine_instance :=
  {|
    cdi_bridge_base := packed_mask_bridge_base sm;
    cdi_source := PMS.sm_S sm;
    cdi_target := PMS.sm_T sm;
    cdi_modulus := carryless_square_modulus (packed_mask_bridge_base sm);
    cdi_bridge_R :=
      carryless_bridge_R
        (packed_mask_bridge_base sm) (PMS.sm_S sm) (PMS.sm_T sm);
    cdi_central_binomial :=
      central_binomial
        (carryless_bridge_R
          (packed_mask_bridge_base sm) (PMS.sm_S sm) (PMS.sm_T sm))
  |}.

(*
│
│          The divisibility constraint is the Diophantine surface
│          condition for the compiled instance.
│
*)

(*                         DivConstraint(inst) ⇔ M∣C                          *)

Definition packed_mask_divisibility_constraint
    (inst : carryless_diophantine_instance) : Prop :=
  dividesN (cdi_modulus inst) (cdi_central_binomial inst).

(*
│
│          A stacked mask bridge is well formed when its bridge base,
│          source, and target form a carryless-binomial instance.
│
*)

(*                 StackBridgeWF(sm) ⇔ WF(BridgeBase(sm),S,T)                 *)

Definition stacked_mask_bridge_wf (sm : stacked_mask_instance) : Prop :=
  carryless_binomial_wf
    (packed_mask_bridge_base sm) (PMS.sm_S sm) (PMS.sm_T sm).

(*
│
│          The compiler well-formedness contract preserves instance
│          well-formedness from a well-formed mask stack.
│
*)

(*                   MaskStackWF ⇒ InstanceWF(Compile(sm))                    *)

Definition carryless_to_diophantine_compiler_wf
    (compile : stacked_mask_instance -> carryless_diophantine_instance) : Prop :=
  forall p b v sm,
    mask_stack_wf p b v sm ->
    carryless_diophantine_wf (compile sm).

(*
│
│          The compiler soundness contract maps a true packed mask
│          constraint to the divisibility constraint.
│
*)

(*               StackBridgeWF ∧ MaskConstraint ⇒ DivConstraint               *)

Definition carryless_to_diophantine_compiler_sound
    (compile : stacked_mask_instance -> carryless_diophantine_instance) : Prop :=
  forall sm,
    stacked_mask_bridge_wf sm ->
    packed_mask_stack_constraint sm ->
    packed_mask_divisibility_constraint (compile sm).

(*
│
│          The compiler completeness contract maps the divisibility
│          constraint back to the packed mask constraint.
│
*)

(*               StackBridgeWF ∧ DivConstraint ⇒ MaskConstraint               *)

Definition carryless_to_diophantine_compiler_complete
    (compile : stacked_mask_instance -> carryless_diophantine_instance) : Prop :=
  forall sm,
    stacked_mask_bridge_wf sm ->
    packed_mask_divisibility_constraint (compile sm) ->
    packed_mask_stack_constraint sm.

(*
│
│          Compiler correctness packages soundness and completeness.
│
*)

(*                         Correct ⇔ Sound ∧ Complete                         *)

Definition carryless_to_diophantine_compiler_correct
    (compile : stacked_mask_instance -> carryless_diophantine_instance) : Prop :=
  carryless_to_diophantine_compiler_sound compile /\
  carryless_to_diophantine_compiler_complete compile.

(*
│
│          The full compiler contract packages well-formedness and
│          correctness.
│
*)

(*                       WithWF ⇔ WFContract ∧ Correct                        *)

Definition carryless_to_diophantine_compiler_with_wf
    (compile : stacked_mask_instance -> carryless_diophantine_instance) : Prop :=
  carryless_to_diophantine_compiler_wf compile /\
  carryless_to_diophantine_compiler_correct compile.

(*
│
│          The square modulus unfolds to the product of the bridge
│          base with itself.
│
*)

(*                                   B²=B·B                                   *)

Lemma carryless_square_modulus_unfold :
  forall B,
    carryless_square_modulus B = B * B.
Proof.
  reflexivity.
Qed.

(*
│
│          The bridge argument unfolds to its source-target polynomial
│          expression.
│
*)

(*                       R(B,S,T)=S·(B²−B)+(T+1)·(B²−1)                       *)

Lemma carryless_bridge_R_unfold :
  forall B S T,
    carryless_bridge_R B S T =
    S * (carryless_square_modulus B - B) +
    (T + 1) * (carryless_square_modulus B - 1).
Proof.
  reflexivity.
Qed.

(*
│
│          Every power-of-two base is positive.
│
*)

(*                               pow₂(B) ⇒ 0<B                                *)

Lemma pow2_positive :
  forall B,
    pow2 B ->
    0 < B.
Proof.
  intros B Hpow.
  destruct Hpow as [k ->].
  pose proof (CC.pow2_lower_bound k).
  lia.
Qed.

(*
│
│          The product of two power-of-two values is again a power of
│          two.
│
*)

(*                       pow₂(A) ∧ pow₂(B) ⇒ pow₂(A·B)                        *)

Lemma pow2_mul :
  forall A B,
    pow2 A ->
    pow2 B ->
    pow2 (A * B).
Proof.
  intros A B [a ->] [b ->].
  exists (a + b).
  rewrite N.pow_add_r.
  reflexivity.
Qed.

(*
│
│          The fifth-power packed bridge base is a power of two
│          whenever the stack base is.
│
*)

(*                     pow₂(stackBase) ⇒ pow₂(stackBase⁵)                     *)

Lemma packed_mask_bridge_base_pow2 :
  forall sm,
    pow2 (PMS.sm_stack_base sm) ->
    pow2 (packed_mask_bridge_base sm).
Proof.
  intros sm Hpow.
  unfold packed_mask_bridge_base.
  repeat apply pow2_mul; exact Hpow.
Qed.

(*
│
│          A well-formed mask stack has a positive stack base.
│
*)

(*                         MaskStackWF ⇒ 0<stackBase                          *)

Lemma mask_stack_wf_base_positive :
  forall p b v sm,
    mask_stack_wf p b v sm ->
    0 < PMS.sm_stack_base sm.
Proof.
  intros p b v sm Hwf.
  destruct Hwf as (Hpow & _).
  apply pow2_positive.
  exact Hpow.
Qed.

(*
│
│          A well-formed mask stack bounds the stacked source below
│          the fifth-power bridge base.
│
*)

(*                         MaskStackWF ⇒ S<BridgeBase                         *)

Lemma mask_stack_wf_source_bound :
  forall p b v sm,
    mask_stack_wf p b v sm ->
    PMS.sm_S sm < packed_mask_bridge_base sm.
Proof.
  intros p b v sm Hwf.
  unfold packed_mask_bridge_base.
  destruct Hwf as
    (Hpow &
     Hstate & _HstateMask &
     Hip & _HipMask &
     Hr1 & _Hr1Mask &
     Hr2 & _Hr2Mask &
     Hhalt & _HhaltMask &
     HS & _HT).
  rewrite HS.
  unfold PMS.packed_mask_stack_source.
  apply PMS.stack5_bound.
  - apply pow2_positive.
    exact Hpow.
  - exact Hstate.
  - exact Hip.
  - exact Hr1.
  - exact Hr2.
  - exact Hhalt.
Qed.

(*
│
│          A well-formed mask stack bounds the stacked target below
│          the fifth-power bridge base.
│
*)

(*                         MaskStackWF ⇒ T<BridgeBase                         *)

Lemma mask_stack_wf_target_bound :
  forall p b v sm,
    mask_stack_wf p b v sm ->
    PMS.sm_T sm < packed_mask_bridge_base sm.
Proof.
  intros p b v sm Hwf.
  unfold packed_mask_bridge_base.
  destruct Hwf as
    (Hpow &
     _Hstate & HstateMask &
     _Hip & HipMask &
     _Hr1 & Hr1Mask &
     _Hr2 & Hr2Mask &
     _Hhalt & HhaltMask &
     _HS & HT).
  rewrite HT.
  unfold PMS.packed_mask_stack_target.
  apply PMS.stack5_bound.
  - apply pow2_positive.
    exact Hpow.
  - exact HstateMask.
  - exact HipMask.
  - exact Hr1Mask.
  - exact Hr2Mask.
  - exact HhaltMask.
Qed.

(*
│
│          A well-formed mask stack induces a well-formed
│          carryless-binomial bridge instance.
│
*)

(*                        MaskStackWF ⇒ StackBridgeWF                         *)

Lemma mask_stack_wf_bridge_wf :
  forall p b v sm,
    mask_stack_wf p b v sm ->
    stacked_mask_bridge_wf sm.
Proof.
  intros p b v sm Hwf.
  pose proof Hwf as Hwf0.
  destruct Hwf as (Hpow & _).
  unfold stacked_mask_bridge_wf, carryless_binomial_wf.
  repeat split.
  - apply packed_mask_bridge_base_pow2.
    exact Hpow.
  - apply mask_stack_wf_source_bound with (p := p) (b := b) (v := v).
    exact Hwf0.
  - apply mask_stack_wf_target_bound with (p := p) (b := b) (v := v).
    exact Hwf0.
Qed.

(*
│
│          A well-formed stacked mask bridge has a positive bridge
│          base.
│
*)

(*                        StackBridgeWF ⇒ 0<BridgeBase                        *)

Lemma stacked_mask_bridge_wf_bridge_base_positive :
  forall sm,
    stacked_mask_bridge_wf sm ->
    0 < packed_mask_bridge_base sm.
Proof.
  intros sm Hwf.
  destruct Hwf as (Hpow & _).
  apply pow2_positive.
  exact Hpow.
Qed.

(*
│
│          The compiled instance modulus is positive under mask-stack
│          well-formedness.
│
*)

(*                    MaskStackWF ⇒ 0<modulus(Compile(sm))                    *)

Lemma mask_stack_wf_modulus_positive :
  forall p b v sm,
    mask_stack_wf p b v sm ->
    0 < cdi_modulus (packed_mask_diophantine_instance_of sm).
Proof.
  intros p b v sm Hwf.
  unfold packed_mask_diophantine_instance_of, cdi_modulus, carryless_square_modulus.
  simpl.
  unfold packed_mask_bridge_base.
  pose proof (mask_stack_wf_base_positive p b v sm Hwf).
  nia.
Qed.

(*
│
│          The compiled divisibility constraint is exactly the
│          carryless binomial target for the packed bridge fields.
│
*)

(*            DivConstraint(Compile(sm)) ⇔ Target(BridgeBase,S,T)             *)

Lemma packed_mask_divisibility_constraint_of :
  forall sm,
    packed_mask_divisibility_constraint (packed_mask_diophantine_instance_of sm) <->
    carryless_binomial_target
      (packed_mask_bridge_base sm) (PMS.sm_S sm) (PMS.sm_T sm).
Proof.
  intro sm.
  unfold packed_mask_divisibility_constraint,
    packed_mask_diophantine_instance_of,
    carryless_binomial_target.
  simpl.
  reflexivity.
Qed.

(*
│
│          The packed-mask compiler satisfies its well-formedness
│          contract.
│
*)

(*                            WFContract(Compile)                             *)

Theorem packed_mask_diophantine_instance_meets_wf_contract :
  carryless_to_diophantine_compiler_wf packed_mask_diophantine_instance_of.
Proof.
  intros p b v sm Hwf.
  unfold carryless_diophantine_wf, packed_mask_diophantine_instance_of.
  simpl.
  split.
  - apply mask_stack_wf_bridge_wf with (p := p) (b := b) (v := v).
    exact Hwf.
  - repeat split; reflexivity.
Qed.

(*
│
│          The packed-mask compiler is sound: mask-stack carrylessness
│          implies the divisibility constraint.
│
*)

(*                               Sound(Compile)                               *)

Theorem packed_mask_diophantine_instance_sound :
  carryless_to_diophantine_compiler_sound packed_mask_diophantine_instance_of.
Proof.
  intros sm Hwf Hcarry.
  apply (proj2 (packed_mask_divisibility_constraint_of sm)).
  apply
    ((proj1 carryless_binomial_bridge_proved)
      (packed_mask_bridge_base sm) (PMS.sm_S sm) (PMS.sm_T sm)).
  - exact Hwf.
  - unfold packed_mask_stack_constraint in Hcarry.
    exact Hcarry.
Qed.

(*
│
│          The packed-mask compiler is complete: the divisibility
│          constraint implies mask-stack carrylessness.
│
*)

(*                             Complete(Compile)                              *)

Theorem packed_mask_diophantine_instance_complete :
  carryless_to_diophantine_compiler_complete packed_mask_diophantine_instance_of.
Proof.
  intros sm Hwf Hdiv.
  unfold packed_mask_stack_constraint.
  apply
    ((proj2 carryless_binomial_bridge_proved)
      (packed_mask_bridge_base sm) (PMS.sm_S sm) (PMS.sm_T sm)).
  - exact Hwf.
  - apply (proj1 (packed_mask_divisibility_constraint_of sm)).
    exact Hdiv.
Qed.

(*
│
│          The packed-mask compiler is correct.
│
*)

(*                              Correct(Compile)                              *)

Theorem packed_mask_diophantine_instance_correct :
  carryless_to_diophantine_compiler_correct packed_mask_diophantine_instance_of.
Proof.
  split.
  - exact packed_mask_diophantine_instance_sound.
  - exact packed_mask_diophantine_instance_complete.
Qed.

(*
│
│          The packed-mask Diophantine instance satisfies the full
│          well-formed correctness contract.
│
*)

(*                              WithWF(Compile)                               *)

Theorem packed_mask_diophantine_instance_with_wf :
  carryless_to_diophantine_compiler_with_wf packed_mask_diophantine_instance_of.
Proof.
  split.
  - apply packed_mask_diophantine_instance_meets_wf_contract.
  - exact packed_mask_diophantine_instance_correct.
Qed.
