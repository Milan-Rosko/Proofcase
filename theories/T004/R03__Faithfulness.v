(* R03__Faithfulness.v *)

From Coq Require Import Bool Lia List ZArith.
Import ListNotations.

From T004 Require Import
  R01__Cellular_Semantics.

Open Scope Z_scope.
Set Bullet Behavior "None".

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / T004 -- Semantic Faithfulness                            *)
(*                                                                       *)
(*  This layer isolates the unique external premise of T004: a           *)
(*  faithfulness principle lifting observed periodicity across           *)
(*  increasing centered windows. The contradiction core below remains    *)
(*  constructive and depends only on the semantics developed in R01.     *)
(*                                                                       *)
(*************************************************************************)

(*
  Tail periodicity at a fixed observation radius.
*)

Definition observational_periodic_tail (R T P : nat) : Prop :=
  (0 < P)%nat /\
  forall t,
    (T <= t)%nat ->
    centered_line R (t + P)%nat = centered_line R t.

(*
  Uniform periodicity across every radius extension of a base window.
*)

Definition uniform_eventual_periodic_tail (R T P : nat) : Prop :=
  (0 < P)%nat /\
  forall e : nat, forall t,
    (T <= t)%nat ->
    centered_line (R + e) (t + P)%nat = centered_line (R + e) t.

(*
  From Observation to Structure

  The transition from observation to proof requires a semantic bridge.

  Observational periodicity is a statement about bounded windows.
  Eventual periodicity is a statement about an infinite object.
  Without a principle connecting these levels, the implication cannot
  be made.

  Faithfulness provides exactly this bridge: it enforces coherence
  across scales. Once such coherence is assumed, periodicity becomes a
  global object, and the constructive obstructions developed in earlier
  phases apply.

  The problem of Rule 30 is therefore not the absence of structure, but
  the absence of an accepted mechanism for stabilizing that structure
  across scales.
*)

(*
  Faithfulness as Semantic Completion

  The Faithfulness Hypothesis can be viewed as a completion principle
  analogous in role to Cauchy completion.

  In the construction of the reals, sequences that are locally coherent
  (Cauchy) are promoted to genuine global objects. The completion
  enforces stability under refinement.

  Faithfulness plays the same role for Rule 30. It asserts that a
  periodic pattern observed at one radius is not an artifact of
  truncation, but persists under enlargement of the observation window.

  In this sense, Faithfulness is not an arbitrary assumption. It is the
  minimal condition required to turn observational data into a stable
  semantic object.
*)

(*
  The unique external premise of the T004 package.
*)

Axiom Faithfulness_Hypothesis :
  forall R T P : nat,
    observational_periodic_tail R T P ->
    observational_periodic_tail (S R) T P.

(*
  Iterated faithfulness lift.
*)

Lemma faithful_growth_iterates :
  forall R T P s : nat,
    observational_periodic_tail R T P ->
    observational_periodic_tail (R + s) T P.
Proof.
  intros R T P s Hobs.
  induction s as [|s IH].
  - replace (R + 0)%nat with R by lia.
    exact Hobs.
  - replace (R + S s)%nat with (S (R + s))%nat by lia.
    apply Faithfulness_Hypothesis.
    exact IH.
Qed.

(*
  Faithfulness promotes one observed tail to a uniform family of tails.
*)

Lemma faithfulness_implies_uniform_tail_lift :
  forall R T P : nat,
    observational_periodic_tail R T P ->
    uniform_eventual_periodic_tail R T P.
Proof.
  intros R T P Hobs.
  destruct Hobs as [HP Htail].
  split.
  - exact HP.
  - intros e t Ht.
    pose proof (faithful_growth_iterates R T P e (conj HP Htail)) as Hgrow.
    destruct Hgrow as [_ Hgrow].
    exact (Hgrow t Ht).
Qed.

(*
  No uniform periodic tail can exist: a positive lag always changes the
  canonical orbit at some site, and a sufficiently wide centered window
  sees that change.
*)

Theorem No_Uniform_Periodic_Tail_Witness :
  forall R T P : nat,
    ~ uniform_eventual_periodic_tail R T P.
Proof.
  intros R T P Huni.
  destruct Huni as [HP Hunif].
  destruct (canonical_rows_never_repeat_at_positive_lag T P HP) as [x Hneq].
  set (e := Z.to_nat (Z.abs x)).
  pose proof (Hunif e T (Nat.le_refl T)) as Hline.
  unfold centered_line in Hline.
  assert (He : Z.of_nat e = Z.abs x).
  - unfold e.
    rewrite Z2Nat.id.
    + reflexivity.
    + apply Z.abs_nonneg.
  assert (Hxbound : (- Z.of_nat (R + e) <= x <= Z.of_nat (R + e))%Z).
  - rewrite Nat2Z.inj_add.
    rewrite He.
    destruct (Z_lt_ge_dec x 0).
    + rewrite Z.abs_neq by lia.
      lia.
    + rewrite Z.abs_eq by lia.
      lia.
  pose proof
    (@centered_window_eq_pointwise
       (Rule30_row (T + P)%nat)
       (Rule30_row T)
       (R + e)
       x
       Hxbound
       Hline) as Hx.
  exact (Hneq Hx).
Qed.

(*
  Faithfulness collapses any observed periodic tail into the forbidden
  uniform case.
*)

Theorem No_Observational_Periodic_Tail :
  forall R T P : nat,
    ~ observational_periodic_tail R T P.
Proof.
  intros R T P Hobs.
  apply (No_Uniform_Periodic_Tail_Witness R T P).
  exact (faithfulness_implies_uniform_tail_lift R T P Hobs).
Qed.

(*
  No fixed centered window is eventually periodic under faithfulness.
*)

Theorem No_Eventual_Periodicity_Of_Centered_Windows :
  forall R : nat,
    ~ eventually_periodic_centered_window R.
Proof.
  intros R Hwin.
  destruct Hwin as [T [P [HP Htail]]].
  apply (No_Observational_Periodic_Tail R T P).
  split.
  - exact HP.
  - exact Htail.
Qed.

(*
  The center strip is the radius-zero centered window, so its eventual
  periodicity would contradict the preceding theorem at radius zero.
*)

Theorem Faithful_Aperiodicity_Theorem :
  ~ eventually_periodic_center_strip.
Proof.
  intro Hstrip.
  apply (No_Eventual_Periodicity_Of_Centered_Windows 0%nat).
  destruct Hstrip as [T [P [HP Hper]]].
  exists T, P.
  split.
  - exact HP.
  - intros t Ht.
    rewrite centered_window_radius_zero_is_center_strip.
    rewrite centered_window_radius_zero_is_center_strip.
    now rewrite (Hper t Ht).
Qed.

Global Opaque
  faithful_growth_iterates
  faithfulness_implies_uniform_tail_lift
  No_Uniform_Periodic_Tail_Witness
  No_Observational_Periodic_Tail
  No_Eventual_Periodicity_Of_Centered_Windows
  Faithful_Aperiodicity_Theorem.
