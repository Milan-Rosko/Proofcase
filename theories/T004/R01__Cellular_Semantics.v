(* R01__Cellular_Semantics.v *)

From Coq Require Import Bool Lia List ZArith.
Import ListNotations.

Open Scope Z_scope.
Set Bullet Behavior "None".

(*************************************************************************)
(*                                                                       *)
(*    Proofcase / T004 -- Cellular Semantics                             *)
(*                                                                       *)
(*    Minimal semantic base for the rebuilt T004 package. The scope is   *)
(*    intentionally narrow: seeded Rule30, finite-support bounds, and    *)
(*    the centered observables needed by the later obstruction layers.   *)
(*                                                                       *)
(*************************************************************************)

Definition bit := bool.

(*
  Canonical documentation for `row`.
*)

Definition row := Z -> bit.

(*
  Canonical documentation for `cellular_rule`.
*)

Definition cellular_rule := bit -> bit -> bit -> bit.

(*
  Canonical documentation for `Rule30`.
*)

Definition Rule30 : cellular_rule :=
  fun a b c =>
    match a, b, c with
    | true, true, true => false
    | true, true, false => false
    | true, false, true => false
    | true, false, false => true
    | false, true, true => true
    | false, true, false => true
    | false, false, true => true
    | false, false, false => false
    end.

(*
  Basic truth-table reductions used throughout T004.
*)

Lemma Rule30_00c :
  forall c : bit,
    Rule30 false false c = c.
Proof.
  intro c.
  destruct c; reflexivity.
Qed.

Lemma Rule30_01c_true :
  forall c : bit,
    Rule30 false true c = true.
Proof.
  intro c.
  destruct c; reflexivity.
Qed.

Lemma Rule30_quiescent :
  Rule30 false false false = false.
Proof.
  reflexivity.
Qed.

(*
  Canonical documentation for `step_of`.
*)

Definition step_of (f : cellular_rule) (r : row) : row :=
  fun x => f (r (x - 1)) (r x) (r (x + 1)).

(*
  Canonical documentation for `iterate_step`.
*)

Fixpoint iterate_step (f : cellular_rule) (t : nat) (r : row) : row :=
  match t with
  | O => r
  | S t' => step_of f (iterate_step f t' r)
  end.

(*
  Canonical documentation for `seed_row`.
*)

Definition seed_row : row :=
  fun x => Z.eqb x 0.

(*
  Canonical documentation for `Rule30_row`.
*)

Definition Rule30_row (t : nat) : row :=
  iterate_step Rule30 t seed_row.

(*
  Canonical documentation for `canonical_row`.
*)

Definition canonical_row : nat -> row :=
  Rule30_row.

(*
  Canonical documentation for `supported_in`.
*)

Definition supported_in (n : nat) (r : row) : Prop :=
  forall x,
    (x < - Z.of_nat n \/ Z.of_nat n < x)%Z ->
    r x = false.

(*
  Canonical documentation for `finitely_supported`.
*)

Definition finitely_supported (r : row) : Prop :=
  exists N : nat, supported_in N r.

(*
  Canonical documentation for `centered_window`.
*)

Definition centered_window (r : row) (n : nat) : list bit :=
  map (fun j => r (Z.of_nat j - Z.of_nat n)%Z) (seq 0 (2 * n + 1)).

(*
  Canonical documentation for `centered_line`.
*)

Definition centered_line (n t : nat) : list bit :=
  centered_window (Rule30_row t) n.

(*
  Canonical documentation for `center_strip`.
*)

Definition center_strip (t : nat) : bit :=
  Rule30_row t 0%Z.

(*
  Canonical documentation for `eventually_periodic_center_strip`.
*)

Definition eventually_periodic_center_strip : Prop :=
  exists T P : nat,
    (0 < P)%nat /\
    forall t,
      (T <= t)%nat ->
      center_strip (t + P)%nat = center_strip t.

(*
  Canonical documentation for `eventually_periodic_centered_window`.
*)

Definition eventually_periodic_centered_window (R : nat) : Prop :=
  exists T P : nat,
    (0 < P)%nat /\
    forall t,
      (T <= t)%nat ->
      centered_line R (t + P)%nat = centered_line R t.

(*
  Canonical documentation for `eventually_periodic_full_rows`.
*)

Definition eventually_periodic_full_rows : Prop :=
  exists T P : nat,
    (0 < P)%nat /\
    forall t,
      (T <= t)%nat ->
      forall x : Z,
        Rule30_row (t + P)%nat x = Rule30_row t x.

(*
  Canonical documentation for `canonical_row_seed_at_time_zero`.
*)

Lemma canonical_row_seed_at_time_zero :
  forall x,
    Rule30_row 0%nat x = seed_row x.
Proof.
  intro x.
  unfold Rule30_row.
  simpl.
  reflexivity.
Qed.

(*
  Canonical documentation for `canonical_row_step`.
*)

Lemma canonical_row_step :
  forall t x,
    Rule30_row (S t) x = step_of Rule30 (Rule30_row t) x.
Proof.
  intros t x.
  unfold Rule30_row.
  simpl.
  reflexivity.
Qed.

(*
  Canonical documentation for `nth_error_centered_window`.
*)

Lemma nth_error_centered_window :
  forall r n j,
    (j < 2 * n + 1)%nat ->
    nth_error (centered_window r n) j =
    Some (r (Z.of_nat j - Z.of_nat n)%Z).
Proof.
  intros r n j Hj.
  unfold centered_window.
  rewrite nth_error_map.
  rewrite nth_error_seq.
  assert ((j <? 2 * n + 1)%nat = true).
  - apply Nat.ltb_lt.
    exact Hj.
  rewrite H.
  simpl.
  reflexivity.
Qed.

(*
  Canonical documentation for `centered_window_eq_pointwise`.
*)

Lemma centered_window_eq_pointwise :
  forall r s n x,
    (- Z.of_nat n <= x <= Z.of_nat n)%Z ->
    centered_window r n = centered_window s n ->
    r x = s x.
Proof.
  intros r s n x Hx Heq.
  set (j := Z.to_nat (x + Z.of_nat n)).
  assert (Hjz : (Z.of_nat j = x + Z.of_nat n)%Z).
  - unfold j.
    apply Z2Nat.id.
    lia.
  assert (Hj : (j < 2 * n + 1)%nat).
  - apply Nat2Z.inj_lt.
    rewrite Hjz.
    lia.
  pose proof (nth_error_centered_window r n j Hj) as Hr.
  pose proof (nth_error_centered_window s n j Hj) as Hs.
  rewrite Heq in Hr.
  rewrite Hs in Hr.
  injection Hr as Hval.
  assert (Z.of_nat j - Z.of_nat n = x)%Z.
  - rewrite Hjz.
    lia.
  now rewrite H in Hval.
Qed.

(*
  Canonical documentation for `centered_window_radius_zero_is_center_strip`.
*)

Lemma centered_window_radius_zero_is_center_strip :
  forall t,
    centered_line 0%nat t = [center_strip t].
Proof.
  intro t.
  unfold centered_line, center_strip, centered_window.
  simpl.
  replace (Z.of_nat 0 - Z.of_nat 0)%Z with 0%Z by lia.
  reflexivity.
Qed.

(*
  Canonical documentation for
  `centered_line_radius_zero_period_iff_center_strip_period`.
*)

Lemma centered_line_radius_zero_period_iff_center_strip_period :
  forall P,
    (forall t,
       centered_line 0%nat (t + P)%nat =
       centered_line 0%nat t) <->
    (forall t,
       center_strip (t + P)%nat =
       center_strip t).
Proof.
  intro P.
  split.
  - intros Hline t.
    pose proof (Hline t) as H.
    rewrite centered_window_radius_zero_is_center_strip in H.
    rewrite centered_window_radius_zero_is_center_strip in H.
    inversion H.
    reflexivity.
  - intros Hstrip t.
    rewrite centered_window_radius_zero_is_center_strip.
    rewrite centered_window_radius_zero_is_center_strip.
    now rewrite Hstrip.
Qed.

(*
  Canonical documentation for `seed_supported_in_0`.
*)

Lemma seed_supported_in_0 :
  supported_in 0 seed_row.
Proof.
  intros x Hout.
  unfold seed_row.
  apply Z.eqb_neq.
  lia.
Qed.

(*
  Canonical documentation for `supported_step`.
*)

Lemma supported_step :
  forall f n r,
    f false false false = false ->
    supported_in n r ->
    supported_in (S n) (step_of f r).
Proof.
  intros f n r H000 Hsupp x Hout.
  unfold step_of.
  assert (Hxm1 : (x - 1 < - Z.of_nat n \/ Z.of_nat n < x - 1)%Z) by lia.
  assert (Hx : (x < - Z.of_nat n \/ Z.of_nat n < x)%Z) by lia.
  assert (Hxp1 : (x + 1 < - Z.of_nat n \/ Z.of_nat n < x + 1)%Z) by lia.
  rewrite (Hsupp (x - 1)%Z Hxm1).
  rewrite (Hsupp x Hx).
  rewrite (Hsupp (x + 1)%Z Hxp1).
  exact H000.
Qed.

(*
  Canonical documentation for `Rule30_supported`.
*)

Lemma Rule30_supported :
  forall t,
    supported_in t (Rule30_row t).
Proof.
  induction t as [|t IH].
  - unfold Rule30_row.
    simpl.
    exact seed_supported_in_0.
  - unfold Rule30_row in *.
    simpl.
    apply supported_step.
    + exact Rule30_quiescent.
    + exact IH.
Qed.

(*
  The left edge of the canonical light cone is always active.
*)

Lemma left_edge_of_canonical_cone_is_active :
  forall t : nat,
    Rule30_row t (- Z.of_nat t)%Z = true.
Proof.
  induction t as [|t IH].
  - rewrite canonical_row_seed_at_time_zero.
    unfold seed_row.
    replace (- Z.of_nat 0)%Z with 0%Z by lia.
    reflexivity.
  - rewrite canonical_row_step.
    unfold step_of.
    assert (Hleft : Rule30_row t (- Z.of_nat (S t) - 1)%Z = false).
    - apply Rule30_supported.
      lia.
    assert (Hmid : Rule30_row t (- Z.of_nat (S t))%Z = false).
    - apply Rule30_supported.
      lia.
    assert (Hright : Rule30_row t (- Z.of_nat (S t) + 1)%Z = true).
    - replace (- Z.of_nat (S t) + 1)%Z with (- Z.of_nat t)%Z by lia.
      exact IH.
    rewrite Hleft, Hmid, Hright.
    now rewrite Rule30_00c.
Qed.

(*
  Canonical rows differ at every positive lag.
*)

Lemma canonical_rows_never_repeat_at_positive_lag :
  forall T P : nat,
    (0 < P)%nat ->
    exists x : Z,
      Rule30_row (T + P)%nat x <> Rule30_row T x.
Proof.
  intros T P HP.
  exists (- Z.of_nat (T + P))%Z.
  intro Heq.
  rewrite left_edge_of_canonical_cone_is_active in Heq.
  assert
    (Hout :
      (- Z.of_nat (T + P) < - Z.of_nat T \/
       Z.of_nat T < - Z.of_nat (T + P))%Z).
  - lia.
  pose proof (Rule30_supported T (- Z.of_nat (T + P))%Z Hout) as Hsupp.
  rewrite Hsupp in Heq.
  discriminate Heq.
Qed.

(*
  Uniform centered-window tails force full-row periodicity.
*)

Lemma uniform_tail_implies_full_row_periodicity :
  forall T P : nat,
    (0 < P)%nat ->
    (forall R : nat, forall t,
       (T <= t)%nat ->
       centered_line R (t + P)%nat = centered_line R t) ->
    forall t, (T <= t)%nat ->
      forall x : Z,
        Rule30_row (t + P)%nat x = Rule30_row t x.
Proof.
  intros T P _ Htail t Ht x.
  set (R := Z.to_nat (Z.abs x)).
  assert (HR : Z.of_nat R = Z.abs x).
  - unfold R.
    rewrite Z2Nat.id.
    + reflexivity.
    + apply Z.abs_nonneg.
  assert (Hx : (- Z.of_nat R <= x <= Z.of_nat R)%Z).
  - rewrite HR.
    destruct (Z_lt_ge_dec x 0).
    + rewrite Z.abs_neq by lia.
      lia.
    + rewrite Z.abs_eq by lia.
      lia.
  unfold centered_line in Htail.
  eapply (@centered_window_eq_pointwise
            (Rule30_row (t + P)%nat)
            (Rule30_row t)
            R
            x).
  - exact Hx.
  - exact (Htail R t Ht).
Qed.

(* ---- Backward compatibility aliases ---- *)

Definition local_rule := cellular_rule.
Definition iter_row_of := iterate_step.
Definition seed := seed_row.

Definition canonical_row_of (f : cellular_rule) (t : nat) : row :=
  iterate_step f t seed_row.

Definition canonical_center_strip := center_strip.
Definition canonical_centered_line := centered_line.
Definition Rule30_row_zero_eq_seed := canonical_row_seed_at_time_zero.
Definition Rule30_row_successor := canonical_row_step.
Definition canonical_centered_line_0_eq_center_strip :=
  centered_window_radius_zero_is_center_strip.
Definition canonical_centered_line0_period_iff_center_strip_period :=
  centered_line_radius_zero_period_iff_center_strip_period.

Global Opaque
  Rule30_00c
  Rule30_01c_true
  Rule30_quiescent
  canonical_row_seed_at_time_zero
  canonical_row_step
  nth_error_centered_window
  centered_window_eq_pointwise
  centered_window_radius_zero_is_center_strip
  centered_line_radius_zero_period_iff_center_strip_period
  seed_supported_in_0
  supported_step
  Rule30_supported
  left_edge_of_canonical_cone_is_active
  canonical_rows_never_repeat_at_positive_lag
  uniform_tail_implies_full_row_periodicity.
