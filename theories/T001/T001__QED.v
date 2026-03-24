(* T001__QED.v *)

From Coq Require Import Arith Bool Extraction List PeanoNat.
Import ListNotations.

From T001 Require Import
  R01__Carryless_Pairing_Definitions
  R02__Carryless_Pairing_Correctness
  R03__Carryless_Pairing_Examples
  R04__Carryless_P0_Correctness.

(*************************************************************************)
(*                                                                       *)
(*    ________________________  _________________                        *)
(*    ___________________  __ \ ___  ____/__  __ \                       *)
(*    __________________  / / / __  __/  __  / / /                       *)
(*    _________________/ /_/ /___  /______  /_/ /__                      *)
(*    _________________\___\_\(_)_____/(_)_____/_(_)                     *)
(*                                                                       *)
(*    Proofcase / T001 -- QED Surface                                    *)
(*                                                                       *)
(*    This file states an exact public target, the Rocq-side criteria    *)
(*    required  by  the reductions, certifies each endpoint by direct    *)
(*    reuse, and exposes the key assumption reports.                     *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                              PROPOSITIO                               *)
(*                                                                       *)
(*************************************************************************)

(*
  CARRYLESS PAIRING  (Abstract Rocq criterion surface)

  The correctness route is intentionally parameterized by a carryless pack
  `P : Params`. The proof obligations are exactly three Zeckendorf criteria:

    (C1) Sound representation:
         forall n, sum_fib (Z P n) = n.

    (C2) Even-band recovery:
         filtering the support of `pair P x y` on even indices returns
         `even_band P x`.

    (C3) Odd-band recovery:
         filtering the support of `pair P x y` on odd indices above `B P x`
         returns `odd_band P x y`.

  Under these criteria, T001 guarantees two endpoints:

    (E1) Left-inverse endpoint:
         forall x y, unpair P (pair P x y) = (x, y).

    (E2) Injectivity endpoint:
         pair P x1 y1 = pair P x2 y2 -> x1 = x2 /\ y1 = y2.
*)

Definition criterion_Z_sound (P : Params) : Prop :=
  forall n, sum_fib (Z P n) = n.

Definition criterion_Z_even_split (P : Params) : Prop :=
  forall x y,
    filter is_even (Z P (pair P x y)) = even_band P x.

Definition criterion_Z_odd_split (P : Params) : Prop :=
  forall x y,
    filter (odd_ge_B1 (B P x)) (Z P (pair P x y)) = odd_band P x y.

Definition carryless_P0 : Params :=
  R03__Carryless_Pairing_Examples.Realization.P0.

Definition PROPOSITIO : Prop :=
  forall P,
    criterion_Z_sound P ->
    criterion_Z_even_split P ->
    criterion_Z_odd_split P ->
    (forall x y, unpair P (pair P x y) = (x, y)) /\
    (forall x1 y1 x2 y2,
      pair P x1 y1 = pair P x2 y2 ->
      x1 = x2 /\ y1 = y2).

Definition PROPOSITIO_P0 : Prop :=
  (forall x y, unpair carryless_P0 (pair carryless_P0 x y) = (x, y)) /\
  (forall x1 y1 x2 y2,
    pair carryless_P0 x1 y1 = pair carryless_P0 x2 y2 ->
    x1 = x2 /\ y1 = y2).

(*************************************************************************)
(*                                                                       *)
(*                                Q.E.D.                                 *)
(*                                                                       *)
(*************************************************************************)

Theorem unpair_pair_QED :
  forall P,
    criterion_Z_sound P ->
    criterion_Z_even_split P ->
    criterion_Z_odd_split P ->
    forall x y, unpair P (pair P x y) = (x, y).
Proof.
  intros P Hsound Heven Hodd.
  exact (unpair_pair P Hsound Heven Hodd).
Qed.

Theorem pair_inj_QED :
  forall P,
    criterion_Z_sound P ->
    criterion_Z_even_split P ->
    criterion_Z_odd_split P ->
    forall x1 y1 x2 y2,
      pair P x1 y1 = pair P x2 y2 ->
      x1 = x2 /\ y1 = y2.
Proof.
  intros P Hsound Heven Hodd.
  exact (pair_inj P Hsound Heven Hodd).
Qed.

Theorem carryless_pairing_QED : PROPOSITIO.
Proof.
  intros P Hsound Heven Hodd.
  split.
  - exact (unpair_pair_QED P Hsound Heven Hodd).
  - exact (pair_inj_QED P Hsound Heven Hodd).
Qed.

Theorem unpair_pair_P0_QED :
  forall x y, unpair carryless_P0 (pair carryless_P0 x y) = (x, y).
Proof.
  exact unpair_pair_P0.
Qed.

Theorem pair_inj_P0_QED :
  forall x1 y1 x2 y2,
    pair carryless_P0 x1 y1 = pair carryless_P0 x2 y2 ->
    x1 = x2 /\ y1 = y2.
Proof.
  exact pair_inj_P0.
Qed.

Theorem carryless_pairing_P0_QED : PROPOSITIO_P0.
Proof.
  split.
  - exact unpair_pair_P0_QED.
  - exact pair_inj_P0_QED.
Qed.

Print Assumptions unpair_pair_QED.
Print Assumptions pair_inj_QED.
Print Assumptions carryless_pairing_QED.
Print Assumptions unpair_pair_P0_QED.
Print Assumptions pair_inj_P0_QED.
Print Assumptions carryless_pairing_P0_QED.

Redirect "theories/T001/appendix/assumptions/unpair_pair_QED"
  Print Assumptions unpair_pair_QED.
Redirect "theories/T001/appendix/assumptions/pair_inj_QED"
  Print Assumptions pair_inj_QED.
Redirect "theories/T001/appendix/assumptions/carryless_pairing_QED"
  Print Assumptions carryless_pairing_QED.
Redirect "theories/T001/appendix/assumptions/unpair_pair_P0_QED"
  Print Assumptions unpair_pair_P0_QED.
Redirect "theories/T001/appendix/assumptions/pair_inj_P0_QED"
  Print Assumptions pair_inj_P0_QED.
Redirect "theories/T001/appendix/assumptions/carryless_pairing_P0_QED"
  Print Assumptions carryless_pairing_P0_QED.

(*************************************************************************)
(*                                                                       *)
(*                           OCaml Extraction                            *)
(*                                                                       *)
(*************************************************************************)

Section Extraction_Interface.

(*
  (1)
  Fibonacci data at index n.
*)

Definition carryless_fib_data (n : nat) : nat * nat :=
  fib_pair n.

(*
  (2)
  Concrete Zeckendorf support extractor for the distinguished realization.
*)

Definition carryless_support_P0 (n : nat) : list nat :=
  Z carryless_P0 n.

(*
  (3)
  Concrete rank function for the distinguished realization.
*)

Definition carryless_rank_P0 (n : nat) : nat :=
  r carryless_P0 n.

(*
  (4)
  Even-band projection specialized to `P0`.
*)

Definition carryless_even_band_P0 (x : nat) : list nat :=
  even_band carryless_P0 x.

(*
  (5)
  Odd-band projection specialized to `P0`.
*)

Definition carryless_odd_band_P0 (x y : nat) : list nat :=
  odd_band carryless_P0 x y.

(*
  (6)
  Carryless pairing specialized to `P0`.
*)

Definition carryless_pair_P0 (x y : nat) : nat :=
  pair carryless_P0 x y.

(*
  (7)
  Zeckendorf support of the encoded pair value.
*)

Definition carryless_encoded_support_P0 (x y : nat) : list nat :=
  carryless_support_P0 (carryless_pair_P0 x y).

(*
  (8)
  Carryless unpairing specialized to `P0`.
*)

Definition carryless_unpair_P0 (n : nat) : nat * nat :=
  unpair carryless_P0 n.

(*
  (9)
  One-step roundtrip utility for the concrete instance.
*)

Definition carryless_roundtrip_P0 (x y : nat) : nat * nat :=
  carryless_unpair_P0 (carryless_pair_P0 x y).

(*
  (10)
  Boolean check that the roundtrip returns the original inputs.
*)

Definition carryless_roundtrip_okb_P0 (x y : nat) : bool :=
  match carryless_roundtrip_P0 x y with
  | (x', y') => andb (Nat.eqb x x') (Nat.eqb y y')
  end.

End Extraction_Interface.

Set Extraction Output Directory "T001_Extraction".
Extraction Language OCaml.

Extraction "Carryless_Pairing.ml"
  fib_pair
  fib
  sum_fib
  two
  two_j_minus1
  is_even
  is_odd
  div2
  R03__Carryless_Pairing_Examples.Realization.find_r_aux
  R03__Carryless_Pairing_Examples.Realization.r0
  R03__Carryless_Pairing_Examples.Realization.zeck_greedy_down
  R03__Carryless_Pairing_Examples.Realization.Z0
  carryless_P0
  carryless_fib_data
  carryless_support_P0
  carryless_rank_P0
  even_band
  odd_band
  carryless_even_band_P0
  carryless_odd_band_P0
  pair
  carryless_pair_P0
  carryless_encoded_support_P0
  unpair
  carryless_unpair_P0
  carryless_roundtrip_P0
  carryless_roundtrip_okb_P0.

(*
  ASSUMPTION REPORT

  The abstract QED surface (`unpair_pair_QED`, `pair_inj_QED`) is explicitly
  parameterized by the three Rocq criteria in `PROPOSITIO`.

  The concrete `P0` examples remain closed vm_compute witnesses.
*)

Print Assumptions
  R03__Carryless_Pairing_Examples.Examples.test_unpair_pair_5_3.
