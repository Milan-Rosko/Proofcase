(* R04__Carryless_P0_Correctness.v *)

From Coq Require Import Arith Bool List PeanoNat.
Import ListNotations.

From T001 Require Import
  R01__Carryless_Pairing_Definitions
  R02__Carryless_Pairing_Correctness
  R03__Carryless_Pairing_Examples.
From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf.

(*************************************************************************)
(*                                                                       *)
(*    Proofcase / T001 -- Concrete P0 Closure                            *)
(*                                                                       *)
(*    This file discharges the abstract Zeckendorf criteria for the      *)
(*    concrete `P0` realization used in T001, yielding premise-free      *)
(*    carryless pairing endpoints for that distinguished instance.       *)
(*                                                                       *)
(*************************************************************************)

Module CP := R01__Carryless_Pairing_Definitions.
Module CPC := R02__Carryless_Pairing_Correctness.
Module P0R := R03__Carryless_Pairing_Examples.Realization.
Module FF := R01__Foundation_Fibonacci.
Module FZ := R02__Foundation_Zeckendorf.

Lemma fib_pair_bridge :
  forall n, CP.fib_pair n = FF.fib_pair n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma fib_bridge :
  forall n, CP.fib n = FF.fib n.
Proof.
  intro n.
  unfold CP.fib, FF.fib.
  rewrite fib_pair_bridge.
  reflexivity.
Qed.

Lemma sum_fib_bridge :
  forall xs, CP.sum_fib xs = FF.sum_fib xs.
Proof.
  induction xs as [|k xs IH].
  - reflexivity.
  - simpl. rewrite fib_bridge, IH. reflexivity.
Qed.

Lemma two_j_minus1_bridge :
  forall j, CP.two_j_minus1 j = FF.two_j_minus1 j.
Proof.
  intro j.
  unfold CP.two_j_minus1, FF.two_j_minus1, CP.two, FF.two.
  reflexivity.
Qed.

Lemma is_even_bridge :
  forall n, CP.is_even n = FF.is_even n.
Proof.
  fix IH 1.
  intro n.
  destruct n as [|[|n']].
  - reflexivity.
  - reflexivity.
  - simpl. apply IH.
Qed.

Lemma is_odd_bridge :
  forall n, CP.is_odd n = FF.is_odd n.
Proof.
  intro n.
  unfold CP.is_odd, FF.is_odd.
  rewrite is_even_bridge.
  reflexivity.
Qed.

Lemma div2_bridge :
  forall n, CP.div2 n = FF.div2 n.
Proof.
  fix IH 1.
  intro n.
  destruct n as [|[|n']].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma r0_bridge :
  forall x, P0R.r0 x = FZ.r0 x.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma Z0_bridge :
  forall x, P0R.Z0 x = FZ.Z0 x.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma B_P0_bridge :
  forall x, CP.B P0R.P0 x = FF.B FZ.P0 x.
Proof.
  intro x.
  unfold CP.B, FF.B, P0R.P0, FZ.P0.
  reflexivity.
Qed.

Lemma even_band_P0_bridge :
  forall x, CP.even_band P0R.P0 x = FF.even_band FZ.P0 x.
Proof.
  intro x.
  unfold CP.even_band, FF.even_band, P0R.P0, FZ.P0.
  simpl.
  rewrite Z0_bridge.
  reflexivity.
Qed.

Lemma odd_band_P0_bridge :
  forall x y, CP.odd_band P0R.P0 x y = FF.odd_band FZ.P0 x y.
Proof.
  intros x y.
  unfold CP.odd_band, FF.odd_band, P0R.P0, FZ.P0.
  reflexivity.
Qed.

Lemma pair_P0_bridge :
  forall x y, CP.pair P0R.P0 x y = FF.pair FZ.P0 x y.
Proof.
  intros x y.
  unfold CP.pair, FF.pair.
  rewrite sum_fib_bridge.
  rewrite even_band_P0_bridge, odd_band_P0_bridge.
  reflexivity.
Qed.

Lemma odd_ge_B1_bridge :
  forall Bx k, CP.odd_ge_B1 Bx k = FF.odd_ge_B1 Bx k.
Proof.
  intros Bx k.
  unfold CP.odd_ge_B1, FF.odd_ge_B1.
  rewrite is_odd_bridge.
  reflexivity.
Qed.

Lemma filter_bridge :
  forall (A : Type) (p q : A -> bool) xs,
    (forall a, p a = q a) ->
    filter p xs = filter q xs.
Proof.
  intros A p q xs Hp.
  induction xs as [|a xs IH].
  - reflexivity.
  - simpl.
    rewrite (Hp a), IH.
    reflexivity.
Qed.

Theorem P0_Z_sound :
  forall n, CP.sum_fib (CP.Z P0R.P0 n) = n.
Proof.
  intro n.
  unfold P0R.P0.
  simpl.
  rewrite Z0_bridge.
  rewrite sum_fib_bridge.
  exact (FZ.Z0_sound n).
Qed.

Theorem P0_Z_even_split :
  forall x y,
    filter CP.is_even (CP.Z P0R.P0 (CP.pair P0R.P0 x y)) =
    CP.even_band P0R.P0 x.
Proof.
  intros x y.
  change
    (filter FF.is_even (FZ.Z0 (FF.pair FZ.P0 x y)) =
     FF.even_band FZ.P0 x).
  exact (FZ.Z0_even_split x y).
Qed.

Theorem P0_Z_odd_split :
  forall x y,
    filter (CP.odd_ge_B1 (CP.B P0R.P0 x))
      (CP.Z P0R.P0 (CP.pair P0R.P0 x y)) =
    CP.odd_band P0R.P0 x y.
Proof.
  intros x y.
  change
    (filter (FF.odd_ge_B1 (FF.B FZ.P0 x))
      (FZ.Z0 (FF.pair FZ.P0 x y)) =
     FF.odd_band FZ.P0 x y).
  exact (FZ.Z0_odd_split x y).
Qed.

Theorem unpair_pair_P0 :
  forall x y, CP.unpair P0R.P0 (CP.pair P0R.P0 x y) = (x, y).
Proof.
  exact (CPC.unpair_pair P0R.P0 P0_Z_sound P0_Z_even_split P0_Z_odd_split).
Qed.

Theorem pair_inj_P0 :
  forall x1 y1 x2 y2,
    CP.pair P0R.P0 x1 y1 = CP.pair P0R.P0 x2 y2 ->
    x1 = x2 /\ y1 = y2.
Proof.
  exact (CPC.pair_inj P0R.P0 P0_Z_sound P0_Z_even_split P0_Z_odd_split).
Qed.
