(* R05__Bounds.v *)

From Coq Require Import Arith Bool Lia List Nat ZArith.
Import ListNotations.

From T004 Require Import R01__Cellular_Semantics.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / T004 -- Bounds                                           *)
(*                                                                       *)
(*  This file is purely computational. It packages executable bounded    *)
(*  scans over centered-window tails, radius growth, and period search   *)
(*  profiles. No theorem in the core T004 dependency path relies on      *)
(*  this module.                                                         *)
(*                                                                       *)
(*************************************************************************)

(*
  Epistemic Limits and Periodicity

  The obstruction is ultimately epistemic.

  No finite prefix of a sequence can exclude eventual periodicity. For
  any observed segment, there always exists a periodic extension
  consistent with that segment.

  This is not specific to Rule 30. Even in classical number theory, one
  cannot exclude the possibility that an irrational expansion exhibits
  arbitrarily long periodic-looking segments.

  For example, consider a distant bit position such as
  N = 7,586,401. One could observe a segment
  001001001001001001001001001,
  which appears perfectly periodic, arising from an expression like
  floor(sqrt 2 * 2^N). Such phenomena cannot be ruled out by finite
  inspection alone.

  The impossibility of detecting global nonperiodicity from finite data
  is therefore a general limitation, not a peculiarity of Rule 30.
*)

(*
  Boolean equality on finite bool lists.
*)

Fixpoint list_bool_beq (xs ys : list bool) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Bool.eqb x y && list_bool_beq xs' ys'
  | _, _ => false
  end.

Lemma list_bool_beq_correct :
  forall xs ys,
    list_bool_beq xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys; destruct ys as [|y ys]; simpl.
  - split; intro H.
    + reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate H.
    + discriminate H.
  - split; intro H.
    + discriminate H.
    + discriminate H.
  - split.
    + intro H.
      destruct x, y; simpl in H; try discriminate;
      apply IH in H;
      subst ys;
      reflexivity.
    + intro H.
      inversion H; subst.
      destruct y; simpl.
      * apply IH.
        reflexivity.
      * apply IH.
        reflexivity.
Qed.

(*
  Bounded conjunction over the initial segment [0, n).
*)

Fixpoint forallb_range (f : nat -> bool) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => f n' && forallb_range f n'
  end.

Lemma forallb_range_correct :
  forall (f : nat -> bool) n,
    forallb_range f n = true <->
    (forall t, (t < n)%nat -> f t = true).
Proof.
  intros f n.
  induction n as [|n IH].
  - split.
    + intros _ t Ht.
      lia.
    + intro H.
      reflexivity.
  - simpl.
    rewrite andb_true_iff.
    rewrite IH.
    split.
    + intros [Hn Hall] t Ht.
      assert (t = n \/ t < n)%nat by lia.
      destruct H as [->|Ht'].
      * exact Hn.
      * apply Hall.
        exact Ht'.
    + intro Hall.
      split.
      * apply Hall.
        lia.
      * intros t Ht.
        apply Hall.
        lia.
Qed.

(*
  Bounded observational periodicity at radius R.
*)

Definition bounded_observational_tailb (R T P L : nat) : bool :=
  forallb_range
    (fun t =>
       list_bool_beq
         (centered_line R (T + t + P)%nat)
         (centered_line R (T + t)%nat))
    L.

Lemma bounded_observational_tailb_correct :
  forall R T P L,
    bounded_observational_tailb R T P L = true <->
    (forall t, (t < L)%nat ->
       centered_line R (T + t + P)%nat = centered_line R (T + t)%nat).
Proof.
  intros R T P L.
  unfold bounded_observational_tailb.
  rewrite forallb_range_correct.
  split.
  - intros H t Ht.
    apply list_bool_beq_correct.
    apply H.
    exact Ht.
  - intros H t Ht.
    apply list_bool_beq_correct.
    apply H.
    exact Ht.
Qed.

(*
  Empirical one-step survival of a candidate tail under radius growth.
*)

Definition survives_next_radiusb (R T P L : nat) : bool :=
  bounded_observational_tailb (S R) T P L.

(*
  Consecutive survival depth across increasing radii.
*)

Fixpoint persistence_depth (R T P L extra_max : nat) : nat :=
  match extra_max with
  | O => O
  | S em' =>
      if bounded_observational_tailb R T P L
      then S (persistence_depth (S R) T P L em')
      else O
  end.

(*
  Candidate counting over a finite (T, P) search box.
*)

Fixpoint candidate_count_P (R T Pmax L : nat) : nat :=
  match Pmax with
  | O => O
  | S P' =>
      (if bounded_observational_tailb R T (S P') L then 1 else 0)
      + candidate_count_P R T P' L
  end.

Fixpoint candidate_count (R Tmax Pmax L : nat) : nat :=
  match Tmax with
  | O => O
  | S T' =>
      candidate_count_P R T' Pmax L + candidate_count R T' Pmax L
  end.

(*
  Survival counting over the same search box.
*)

Fixpoint survival_count_P (R T Pmax L : nat) : nat :=
  match Pmax with
  | O => O
  | S P' =>
      (if bounded_observational_tailb R T (S P') L
           && survives_next_radiusb R T (S P') L
       then 1 else 0)
      + survival_count_P R T P' L
  end.

Fixpoint survival_count (R Tmax Pmax L : nat) : nat :=
  match Tmax with
  | O => O
  | S T' =>
      survival_count_P R T' Pmax L + survival_count R T' Pmax L
  end.

Definition survival_rate_num (R Tmax Pmax L : nat) : nat :=
  survival_count R Tmax Pmax L.

Definition survival_rate_den (R Tmax Pmax L : nat) : nat :=
  candidate_count R Tmax Pmax L.

(*
  Largest candidate period whose bounded tail survives to the requested
  empirical depth.
*)

Fixpoint max_stable_period_P
    (R T Pmax L depth best : nat) : nat :=
  match Pmax with
  | O => best
  | S P' =>
      let p := S P' in
      let d := persistence_depth R T p L depth in
      let best' :=
        if (depth <=? d)%nat && (best <? p)%nat then p else best in
      max_stable_period_P R T P' L depth best'
  end.

Fixpoint max_stable_period_T
    (R Tmax Pmax L depth best : nat) : nat :=
  match Tmax with
  | O => best
  | S T' =>
      max_stable_period_T
        R T' Pmax L depth
        (max_stable_period_P R T' Pmax L depth best)
  end.

Definition max_stable_period (R Tmax Pmax L depth : nat) : nat :=
  max_stable_period_T R Tmax Pmax L depth 0.

(*************************************************************************)
(*                                                                       *)
(*                     CONCRETE SCAN PARAMETERS                          *)
(*                                                                       *)
(*************************************************************************)

Definition scan_small_Rmax : nat := 8.
Definition scan_small_Pmax : nat := 128.
Definition scan_small_Tmax : nat := 4096.
Definition scan_small_Lmin_factor : nat := 8.

Definition scan_mid_Rmax : nat := 16.
Definition scan_mid_Pmax : nat := 512.
Definition scan_mid_Tmax : nat := 100000.
Definition scan_mid_Lmin_factor : nat := 16.

Definition scan_stress_Rmax : nat := 24.
Definition scan_stress_Pmax : nat := 64.
Definition scan_stress_Tmax : nat := 1000000.
Definition scan_stress_Lmin_factor : nat := 32.

(*************************************************************************)
(*                                                                       *)
(*                         EXTRACTION INTERFACE                          *)
(*                                                                       *)
(*  These definitions are intended for OCaml extraction via a separate   *)
(*  extraction surface. This file itself contains no extraction         *)
(*  directives.                                                          *)
(*                                                                       *)
(*************************************************************************)
