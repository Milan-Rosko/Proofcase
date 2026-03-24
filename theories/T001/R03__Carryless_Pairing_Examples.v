(*

  Proofcase / T001 / Examples
  ===========================

    Overview
    --------

      We instantiate the carryless pairing interface with a concrete
      Zeckendorf-style realization. The examples in this file are meant to
      be vm_compute-friendly and make the behavior of pair and unpair
      directly inspectable.
*)

From Coq Require Import Arith Bool List PeanoNat.
Import ListNotations.

From T001 Require Import R01__Carryless_Pairing_Definitions.
From T002 Require Import R02__Foundation_Zeckendorf.

Module Realization.

  Definition find_r_aux := R02__Foundation_Zeckendorf.find_r_aux.

  Definition r0 := R02__Foundation_Zeckendorf.r0.

  Definition zeck_greedy_down := R02__Foundation_Zeckendorf.zeck_greedy_down.

  Definition Z0 := R02__Foundation_Zeckendorf.Z0.

  (*
    Concrete parameter pack.
  *)

  Definition P0 : Params :=
    {| Z := Z0; r := r0 |}.

End Realization.

Module Examples.

  Import Realization.

  (*
    Example 1: x = 1, y = 1
  *)

  Example test_pair_1_1_value :
    pair P0 1 1 = 37.
  Proof. vm_compute. reflexivity. Qed.

  Example test_Z_1 :
    Z P0 1 = [2].
  Proof. vm_compute. reflexivity. Qed.

  Example test_r_1 :
    r P0 1 = 3.
  Proof. vm_compute. reflexivity. Qed.

  Example test_B_1 :
    B P0 1 = 6.
  Proof. vm_compute. reflexivity. Qed.

  Example test_even_band_1 :
    even_band P0 1 = [4].
  Proof. vm_compute. reflexivity. Qed.

  Example test_odd_band_1_1 :
    odd_band P0 1 1 = [9].
  Proof. vm_compute. reflexivity. Qed.

  Example test_Z_pair_1_1 :
    Z P0 (pair P0 1 1) = [9; 4].
  Proof. vm_compute. reflexivity. Qed.

  Example test_unpair_pair_1_1 :
    unpair P0 (pair P0 1 1) = (1, 1).
  Proof. vm_compute. reflexivity. Qed.

  (*
    Example 2: x = 5, y = 3
  *)

  Example test_pair_5_3_value :
    pair P0 5 3 = 4236.
  Proof. vm_compute. reflexivity. Qed.

  Example test_unpair_pair_5_3 :
    unpair P0 (pair P0 5 3) = (5, 3).
  Proof. vm_compute. reflexivity. Qed.

End Examples.
