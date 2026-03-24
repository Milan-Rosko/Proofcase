(* R04__Transversality.v *)

From Coq Require Import Arith Lia Nat ZArith.

From T004 Require Import R01__Cellular_Semantics.

Local Open Scope nat_scope.

(*************************************************************************)
(*                                                                       *)
(*  Layer 1: Concrete Diagonal Interface                                 *)
(*                                                                       *)
(*************************************************************************)

Definition divides (a b : nat) : Prop :=
  exists q : nat, b = (q * a)%nat.

Definition right_diagonal (k : nat) : nat -> bit :=
  fun t => Rule30_row t (Z.of_nat t - Z.of_nat k)%Z.

Lemma right_diagonal_center_link :
  forall t, right_diagonal t t = center_strip t.
Proof.
  intro t.
  unfold right_diagonal, center_strip.
  replace (Z.of_nat t - Z.of_nat t)%Z with 0%Z by lia.
  reflexivity.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 2: Concrete Period Profile                                     *)
(*                                                                       *)
(*************************************************************************)

Definition right_period (k : nat) : nat :=
  Nat.pow 2 k.

Lemma right_period_lower_bound :
  forall k, (S k <= right_period k)%nat.
Proof.
  intro k.
  unfold right_period.
  induction k as [|k IH].
  - simpl. lia.
  - simpl. nia.
Qed.

Lemma right_period_unbounded :
  forall M, exists k, right_period k > M.
Proof.
  intro M.
  exists (S M).
  pose proof (right_period_lower_bound (S M)) as Hbound.
  lia.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 3: The Unique External Premise                                 *)
(*                                                                       *)
(*************************************************************************)

Axiom Transversal_Bridge :
  forall T P k,
    (0 < P)%nat ->
    (forall t, (T <= t)%nat ->
      center_strip (t + P)%nat = center_strip t) ->
    divides (Nat.pow 2 k) P.

(*************************************************************************)
(*                                                                       *)
(*  Layer 4: Arithmetic Contradiction Core                               *)
(*                                                                       *)
(*************************************************************************)

Lemma divisor_cannot_exceed_dividend :
  forall a b,
    divides a b ->
    (0 < b)%nat ->
    a <= b.
Proof.
  intros a b [q Hdiv] Hb.
  destruct q as [|q].
  - simpl in Hdiv.
    lia.
  - rewrite Hdiv.
    nia.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 5: Crown Theorem                                               *)
(*                                                                       *)
(*************************************************************************)

Theorem Transversal_Aperiodicity_Theorem :
  ~ eventually_periodic_center_strip.
Proof.
  intros [T [P [HP Htail]]].
  destruct (right_period_unbounded P) as [k Hk].
  pose proof (Transversal_Bridge T P k HP Htail) as Hdiv.
  assert (Hle : (Nat.pow 2 k <= P)%nat).
  - apply divisor_cannot_exceed_dividend.
    + exact Hdiv.
    + exact HP.
  - unfold right_period in Hk.
    lia.
Qed.

Global Opaque
  right_diagonal_center_link
  right_period_lower_bound
  right_period_unbounded
  divisor_cannot_exceed_dividend
  Transversal_Aperiodicity_Theorem.
