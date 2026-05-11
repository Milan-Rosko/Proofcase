(*S003_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / S003_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This premise layer fixes the Rule 30 base semantics and the public
  reduction contract. The semantics are bi-infinite: rows are functions from
  integer sites to Boolean cells, the initial row has exactly one live cell
  at the origin, and `center_column t` reads site `0` at time `t`.

  The public contract is explicit about its premise. The package proves that
  if any eventual center-tail period lifts to matching centered windows of
  every radius with the same cutoff and period, then the Rule 30 center
  column is not eventually periodic.

  This package does not assert the lift premise. It proves that the lift
  premise is sufficient. The remaining public task is to inhabit
  `center_tail_lifts_to_windows`, exposed again as
  `CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION`.

*)

From Stdlib Require Export Arith PeanoNat Bool Lia List ZArith.
Export ListNotations.
Global Open Scope list_scope.
Local Open Scope Z_scope.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                BASE SEMANTICS                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The cell alphabet is Boolean: `true` is live, `false` is
│          quiescent.
│
*)

Definition bit : Type := bool.

(*
│
│          A row is a bi-infinite integer-indexed Boolean
│          configuration.
│
*)

Definition row : Type := Z -> bit.

(*
│
│          A radius-one cellular rule consumes left, center, and right
│          neighbor bits.
│
*)

Definition cellular_rule : Type := bit -> bit -> bit -> bit.

(*
│
│          Rule 30 is fixed extensionally as `left XOR (center OR
│          right)`.
│
*)

Definition Rule30 : cellular_rule :=
  fun left center right => xorb left (orb center right).

(*
│
│          One synchronous global step applies the local rule at every
│          integer site.
│
*)

Definition step_of (f : cellular_rule) (r : row) : row :=
  fun x => f (r (x - 1)%Z) (r x) (r (x + 1)%Z).

(*
│
│          `iterate_step f t r` is the row obtained after `t`
│          synchronous steps from `r`.
│
*)

Fixpoint iterate_step (f : cellular_rule) (t : nat) (r : row) : row :=
  match t with
  | O => r
  | S t' => step_of f (iterate_step f t' r)
  end.

(*
│
│          The canonical seed row has one live cell at the origin and
│          is quiescent elsewhere.
│
*)

Definition seed_row : row :=
  fun x => Z.eqb x 0%Z.

(*
│
│          The canonical Rule 30 row at time `t` is the `t`-fold
│          iterate from the seed row.
│
*)

Definition rule30_row (t : nat) : row :=
  iterate_step Rule30 t seed_row.

(*
│
│          The center column is the time stream obtained by reading
│          site `0`.
│
*)

Definition center_column (t : nat) : bit :=
  rule30_row t 0%Z.

(*
│
│          A centered window of radius `R` reads the interval `[-R,
│          R]` from left to right.
│
*)

Definition centered_window (r : row) (R : nat) : list bit :=
  map (fun j => r (Z.of_nat j - Z.of_nat R)%Z)
      (seq 0 (2 * R + 1)%nat).

(*
│
│          `centered_line R t` is the radius-`R` centered observation
│          at time `t`.
│
*)

Definition centered_line (R t : nat) : list bit :=
  centered_window (rule30_row t) R.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             PERIODICITY CONTRACT                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A center-tail period fixes one positive period after one
│          cutoff.
│
*)

Definition center_tail_period (T P : nat) : Prop :=
  (0 < P)%nat /\
  forall t,
    (T <= t)%nat ->
    center_column (t + P)%nat = center_column t.

(*
│
│          A window-tail period is the corresponding statement for one
│          centered radius.
│
*)

Definition window_tail_period (R T P : nat) : Prop :=
  (0 < P)%nat /\
  forall t,
    (T <= t)%nat ->
    centered_line R (t + P)%nat = centered_line R t.

(*
│
│          The lift premise says that a center-tail period extends to
│          every centered observation radius without changing cutoff
│          or period. The obligation is deliberately uniform: both `T`
│          and `P` are preserved across all radii `R`. A
│          radius-dependent cutoff would not be enough for the
│          light-cone contradiction below.
│
*)

Definition center_tail_lifts_to_windows : Prop :=
  forall T P,
    center_tail_period T P ->
    forall R,
      window_tail_period R T P.

(*
│
│          The center column is eventually periodic when it admits
│          some center-tail period.
│
*)

Definition center_column_eventually_periodic : Prop :=
  exists T P,
    center_tail_period T P.

(*
│
│          The direct center-column answer is the negation of eventual
│          periodicity.
│
*)

Definition CENTER_COLUMN_NONPERIODIC : Prop :=
  ~ center_column_eventually_periodic.

(*
│
│          `wolfram_no_eventual_center_period` states the same
│          challenge in the common `t > i` form.
│
*)

Definition wolfram_no_eventual_center_period : Prop :=
  forall i p,
    (0 < p)%nat ->
    ~ (forall t,
        (i < t)%nat ->
        center_column (t + p)%nat = center_column t).

(*
│
│          Pure periodicity is the special case with cutoff `0`.
│
*)

Definition center_column_purely_periodic : Prop :=
  exists P,
    (0 < P)%nat /\
    forall t,
      center_column (t + P)%nat = center_column t.

(*
│
│          The pure-periodicity corollary is kept separate from the
│          eventual-periodicity contract.
│
*)

Definition CENTER_COLUMN_NOT_PURELY_PERIODIC : Prop :=
  ~ center_column_purely_periodic.

(*
│
│          The challenge claim is the eventual nonperiodicity of the
│          center column.
│
*)

Definition RULE30_PERIODICITY_CHALLENGE : Prop :=
  CENTER_COLUMN_NONPERIODIC.

(*
│
│          This guard names the unconditional challenge claim without
│          certifying it as a package endpoint.
│
*)

Definition UNCONDITIONAL_CHALLENGE_CLAIM : Prop :=
  RULE30_PERIODICITY_CHALLENGE.

(*
│
│          The open lift obligation is the missing interface needed to
│          close the challenge through the reduction below.
│
*)

Definition CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION : Prop :=
  center_tail_lifts_to_windows.

Definition OPEN_LIFT_OBLIGATION : Prop :=
  CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION.

(*
│
│          The reduction contract states that the lift obligation is
│          sufficient for the Rule 30 periodicity challenge.
│
*)

Definition RULE30_REDUCTION_CONTRACT : Prop :=
  CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION ->
  RULE30_PERIODICITY_CHALLENGE.

Definition LIFT_IMPLIES_RULE30_CENTER_NONPERIODIC : Prop :=
  RULE30_REDUCTION_CONTRACT.

(*
│
│          `WITNESS` names the proposition certified by the package.
│
*)

Definition WITNESS : Prop := RULE30_REDUCTION_CONTRACT.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                LIFT INTERFACE                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An implementation of this interface supplies the uniform
│          center-tail-to-window lift obligation.
│
*)

Module Type RULE30_LIFT_INTERFACE.

  Parameter center_tail_lifts_to_windows_certified :
    CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION.

End RULE30_LIFT_INTERFACE.

(*
│
│          The `T <= t` formulation and the common `t > i` formulation
│          define the same eventual nonperiodicity challenge.
│
*)

Theorem center_nonperiodic_iff_wolfram_form :
  CENTER_COLUMN_NONPERIODIC <-> wolfram_no_eventual_center_period.
Proof.
  unfold CENTER_COLUMN_NONPERIODIC,
    center_column_eventually_periodic,
    wolfram_no_eventual_center_period,
    center_tail_period.
  split.
  - intros Hnon i p Hp Htail.
    apply Hnon.
    exists (S i), p.
    split.
    + exact Hp.
    + intros t Ht.
      apply Htail.
      lia.
  - intros Hwol [T [P [HP Htail]]].
    apply (Hwol T P HP).
    intros t Ht.
    apply Htail.
    lia.
Qed.

(*
│
│          Direction from the cutoff formulation to the common `t > i`
│          formulation.
│
*)

Theorem center_nonperiodic_implies_wolfram_form :
  CENTER_COLUMN_NONPERIODIC ->
  wolfram_no_eventual_center_period.
Proof.
  exact (proj1 center_nonperiodic_iff_wolfram_form).
Qed.

(*
│
│          Direction from the common `t > i` formulation back to the
│          cutoff formulation.
│
*)

Theorem wolfram_form_implies_center_nonperiodic :
  wolfram_no_eventual_center_period ->
  CENTER_COLUMN_NONPERIODIC.
Proof.
  exact (proj2 center_nonperiodic_iff_wolfram_form).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             RULE 30 LOCAL FACTS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          With left and center bits both quiescent, Rule 30 copies
│          the right bit.
│
*)

Lemma Rule30_false_false :
  forall c : bit,
    Rule30 false false c = c.
Proof.
  intro c.
  destruct c; reflexivity.
Qed.

(*
│
│          The all-quiescent neighborhood stays quiescent.
│
*)

Lemma Rule30_quiescent :
  Rule30 false false false = false.
Proof.
  reflexivity.
Qed.

(*
│
│          Time zero of the canonical orbit is the seed row.
│
*)

Lemma rule30_row_zero :
  forall x,
    rule30_row 0%nat x = seed_row x.
Proof.
  intro x.
  unfold rule30_row.
  simpl.
  reflexivity.
Qed.

(*
│
│          Successor rows are obtained by one global Rule 30 step.
│
*)

Lemma rule30_row_succ :
  forall t x,
    rule30_row (S t) x = step_of Rule30 (rule30_row t) x.
Proof.
  intros t x.
  unfold rule30_row.
  simpl.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              LIGHT-CONE SUPPORT                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A row is supported in radius `R` when it is quiescent
│          outside `[-R, R]`.
│
*)

Definition supported_in (R : nat) (r : row) : Prop :=
  forall x,
    (x < - Z.of_nat R \/ Z.of_nat R < x)%Z ->
    r x = false.

(*
│
│          The seed row is supported in radius `0`.
│
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
│
│          A quiescent radius-one rule expands support by at most one
│          cell per step.
│
*)

Lemma supported_step :
  forall f R r,
    f false false false = false ->
    supported_in R r ->
    supported_in (S R) (step_of f r).
Proof.
  intros f R r H000 Hsupp x Hout.
  unfold step_of.
  assert (Hleft : (x - 1 < - Z.of_nat R \/ Z.of_nat R < x - 1)%Z) by lia.
  assert (Hcenter : (x < - Z.of_nat R \/ Z.of_nat R < x)%Z) by lia.
  assert (Hright : (x + 1 < - Z.of_nat R \/ Z.of_nat R < x + 1)%Z) by lia.
  rewrite (Hsupp (x - 1)%Z Hleft).
  rewrite (Hsupp x Hcenter).
  rewrite (Hsupp (x + 1)%Z Hright).
  exact H000.
Qed.

(*
│
│          The canonical row at time `t` is supported inside radius
│          `t`.
│
*)

Lemma rule30_row_supported :
  forall t,
    supported_in t (rule30_row t).
Proof.
  induction t as [|t IH].
  - unfold rule30_row.
    simpl.
    exact seed_supported_in_0.
  - unfold rule30_row.
    simpl.
    fold (rule30_row t).
    apply supported_step.
    + exact Rule30_quiescent.
    + exact IH.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              ROW NONREPETITION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The left edge of the canonical light cone is live at every
│          time.
│
*)

Lemma left_edge_of_light_cone_is_live :
  forall t : nat,
    rule30_row t (- Z.of_nat t)%Z = true.
Proof.
  induction t as [|t IH].
  - rewrite rule30_row_zero.
    unfold seed_row.
    replace (- Z.of_nat 0)%Z with 0%Z by lia.
    reflexivity.
  - rewrite rule30_row_succ.
    unfold step_of.
    assert (Hleft : rule30_row t (- Z.of_nat (S t) - 1)%Z = false)
      by (apply rule30_row_supported; lia).
    assert (Hcenter : rule30_row t (- Z.of_nat (S t))%Z = false)
      by (apply rule30_row_supported; lia).
    assert (Hright : rule30_row t (- Z.of_nat (S t) + 1)%Z = true)
      by (replace (- Z.of_nat (S t) + 1)%Z with (- Z.of_nat t)%Z by lia;
          exact IH).
    rewrite Hleft, Hcenter, Hright.
    apply Rule30_false_false.
Qed.

(*
│
│          Canonical rows never repeat at a positive time lag.
│
*)

Theorem canonical_rows_never_repeat_at_positive_lag :
  forall T P : nat,
    (0 < P)%nat ->
    exists x : Z,
      rule30_row (T + P)%nat x <> rule30_row T x.
Proof.
  intros T P HP.
  exists (- Z.of_nat (T + P))%Z.
  intro Heq.
  rewrite left_edge_of_light_cone_is_live in Heq.
  assert
    (Hout :
      (- Z.of_nat (T + P) < - Z.of_nat T \/
       Z.of_nat T < - Z.of_nat (T + P))%Z)
    by lia.
  pose proof (rule30_row_supported T (- Z.of_nat (T + P))%Z Hout) as Hfalse.
  rewrite Hfalse in Heq.
  discriminate Heq.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           CENTERED WINDOWS TO ROWS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Index `j` of a centered window reads site `j - R`.
│
*)

Lemma nth_error_centered_window :
  forall r R j,
    (j < 2 * R + 1)%nat ->
    nth_error (centered_window r R) j =
    Some (r (Z.of_nat j - Z.of_nat R)%Z).
Proof.
  intros r R j Hj.
  unfold centered_window.
  rewrite nth_error_map.
  rewrite nth_error_seq.
  assert (Hltb : (j <? 2 * R + 1)%nat = true)
    by (apply Nat.ltb_lt; exact Hj).
  rewrite Hltb.
  simpl.
  reflexivity.
Qed.

(*
│
│          Equal centered windows agree pointwise throughout their
│          observed interval.
│
*)

Lemma centered_window_eq_pointwise :
  forall r s R x,
    (- Z.of_nat R <= x <= Z.of_nat R)%Z ->
    centered_window r R = centered_window s R ->
    r x = s x.
Proof.
  intros r s R x Hx Heq.
  set (j := Z.to_nat (x + Z.of_nat R)).
  assert (Hjz : (Z.of_nat j = x + Z.of_nat R)%Z)
    by (unfold j; apply Z2Nat.id; lia).
  assert (Hj : (j < 2 * R + 1)%nat)
    by (apply Nat2Z.inj_lt; rewrite Hjz; lia).
  pose proof (nth_error_centered_window r R j Hj) as Hr.
  pose proof (nth_error_centered_window s R j Hj) as Hs.
  rewrite Heq in Hr.
  rewrite Hs in Hr.
  injection Hr as Hval.
  assert (Hjx : (Z.of_nat j - Z.of_nat R = x)%Z)
    by (rewrite Hjz; lia).
  now rewrite Hjx in Hval.
Qed.

(*
│
│          A uniform centered-window tail forces pointwise full-row
│          periodicity.
│
*)

Lemma uniform_centered_windows_imply_full_rows :
  forall T P,
    (forall R t,
      (T <= t)%nat ->
      centered_line R (t + P)%nat = centered_line R t) ->
    forall t,
      (T <= t)%nat ->
      forall x : Z,
        rule30_row (t + P)%nat x = rule30_row t x.
Proof.
  intros T P Htail t Ht x.
  set (R := Z.to_nat (Z.abs x)).
  assert (HR : Z.of_nat R = Z.abs x)
    by (unfold R; rewrite Z2Nat.id; [reflexivity | apply Z.abs_nonneg]).
  assert (Hx : (- Z.of_nat R <= x <= Z.of_nat R)%Z)
    by (rewrite HR;
        destruct (Z_lt_ge_dec x 0);
        [rewrite Z.abs_neq by lia | rewrite Z.abs_eq by lia];
        lia).
  unfold centered_line in Htail.
  eapply (@centered_window_eq_pointwise
            (rule30_row (t + P)%nat)
            (rule30_row t)
            R
            x).
  - exact Hx.
  - exact (Htail R t Ht).
Qed.

(*
│
│          A positive-lag full-row tail contradicts the left-edge
│          nonrepetition theorem.
│
*)

Theorem no_full_row_eventual_period :
  forall T P,
    (0 < P)%nat ->
    ~ (forall t,
        (T <= t)%nat ->
        forall x : Z,
          rule30_row (t + P)%nat x = rule30_row t x).
Proof.
  intros T P HP Htail.
  destruct (canonical_rows_never_repeat_at_positive_lag T P HP) as [x Hneq].
  exact (Hneq (Htail T (Nat.le_refl T) x)).
Qed.

(*
│
│          Consequently no positive-lag tail can repeat at every
│          centered radius.
│
*)

Theorem no_uniform_centered_window_tail :
  forall T P,
    (0 < P)%nat ->
    ~ (forall R t,
        (T <= t)%nat ->
        centered_line R (t + P)%nat = centered_line R t).
Proof.
  intros T P HP Htail.
  apply (no_full_row_eventual_period T P HP).
  exact (uniform_centered_windows_imply_full_rows T P Htail).
Qed.

(*
│
│          This audit theorem is the unconditional row-level
│          obstruction proved by the package.
│
*)

Theorem proved_unconditionally_no_uniform_centered_window_tail :
  forall T P,
    (0 < P)%nat ->
    ~ (forall R t,
        (T <= t)%nat ->
        centered_line R (t + P)%nat = centered_line R t).
Proof.
  exact no_uniform_centered_window_tail.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          PUBLIC CONTRACT DISCHARGE                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The window-lift premise rules out every eventual
│          center-column period.
│
*)

Theorem challenge_from_lift :
  CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION ->
  RULE30_PERIODICITY_CHALLENGE.
Proof.
  unfold CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION,
    RULE30_PERIODICITY_CHALLENGE,
    CENTER_COLUMN_NONPERIODIC,
    center_column_eventually_periodic.
  intros Hlift [T [P Hcenter]].
  destruct Hcenter as [HP Htail].
  pose proof (Hlift T P (conj HP Htail)) as Hwindows.
  apply (no_uniform_centered_window_tail T P HP).
  intros R t Ht.
  destruct (Hwindows R) as [_ HR].
  exact (HR t Ht).
Qed.

Theorem center_tail_window_lift_implies_center_column_nonperiodic :
  RULE30_REDUCTION_CONTRACT.
Proof.
  exact challenge_from_lift.
Qed.

(*
│
│          Given a certified lift implementation, the reduction
│          contract closes the Rule 30 center-column challenge.
│
*)

Module Rule30ChallengeClosed (L : RULE30_LIFT_INTERFACE).

  Theorem rule30_center_column_nonperiodic :
    RULE30_PERIODICITY_CHALLENGE.
  Proof.
    exact (challenge_from_lift L.center_tail_lifts_to_windows_certified).
  Qed.

  Theorem rule30_wolfram_no_eventual_center_period :
    wolfram_no_eventual_center_period.
  Proof.
    exact
      (center_nonperiodic_implies_wolfram_form
         rule30_center_column_nonperiodic).
  Qed.

End Rule30ChallengeClosed.

(*
│
│          Eventual nonperiodicity immediately rules out pure
│          periodicity.
│
*)

Theorem center_column_nonperiodic_implies_not_purely_periodic :
  CENTER_COLUMN_NONPERIODIC ->
  CENTER_COLUMN_NOT_PURELY_PERIODIC.
Proof.
  unfold CENTER_COLUMN_NONPERIODIC,
    center_column_eventually_periodic,
    CENTER_COLUMN_NOT_PURELY_PERIODIC,
    center_column_purely_periodic.
  intros Hnon [P [HP Hperiod]].
  apply Hnon.
  exists 0%nat, P.
  split.
  - exact HP.
  - intros t _.
    exact (Hperiod t).
Qed.

(*
│
│          The same lift premise therefore also rules out pure
│          periodicity.
│
*)

Corollary center_tail_window_lift_implies_not_purely_periodic :
  center_tail_lifts_to_windows ->
  CENTER_COLUMN_NOT_PURELY_PERIODIC.
Proof.
  intro Hlift.
  apply center_column_nonperiodic_implies_not_purely_periodic.
  exact (center_tail_window_lift_implies_center_column_nonperiodic Hlift).
Qed.

(*
│
│          The lift obligation also yields the common `t > i`
│          formulation of center-column nonperiodicity.
│
*)

Theorem wolfram_form_from_lift :
  CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION ->
  wolfram_no_eventual_center_period.
Proof.
  intro Hlift.
  apply center_nonperiodic_implies_wolfram_form.
  exact (challenge_from_lift Hlift).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             AUTOMATION INTERFACE                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Create HintDb rule30_reduction.
Create HintDb rule30_lift.

#[export] Hint Unfold
  RULE30_PERIODICITY_CHALLENGE
  CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION
  : rule30_reduction.

#[export] Hint Resolve
  challenge_from_lift
  center_tail_window_lift_implies_center_column_nonperiodic
  center_column_nonperiodic_implies_not_purely_periodic
  center_tail_window_lift_implies_not_purely_periodic
  center_nonperiodic_implies_wolfram_form
  wolfram_form_implies_center_nonperiodic
  wolfram_form_from_lift
  : rule30_reduction.

(*
│
│          Automation closes the reduction once the lift obligation is
│          supplied.
│
*)

Theorem reduction_contract_by_auto :
  CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION ->
  RULE30_PERIODICITY_CHALLENGE.
Proof.
  auto with rule30_reduction.
Qed.

(*
│
│          The same hint database also closes the common `t > i`
│          formulation once the lift obligation is supplied.
│
*)

Theorem wolfram_form_by_auto :
  CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION ->
  wolfram_no_eventual_center_period.
Proof.
  auto with rule30_reduction.
Qed.

(*
│
│          Audit guard: the reduction hint database does not
│          manufacture the lift obligation.
│
*)

Goal CENTER_TAIL_TO_WINDOWS_LIFT_OBLIGATION.
Proof.
  Fail solve [auto with rule30_reduction].
Abort.

Global Opaque
  center_nonperiodic_iff_wolfram_form
  center_nonperiodic_implies_wolfram_form
  wolfram_form_implies_center_nonperiodic
  Rule30_false_false
  Rule30_quiescent
  rule30_row_zero
  rule30_row_succ
  seed_supported_in_0
  supported_step
  rule30_row_supported
  left_edge_of_light_cone_is_live
  canonical_rows_never_repeat_at_positive_lag
  nth_error_centered_window
  centered_window_eq_pointwise
  uniform_centered_windows_imply_full_rows
  no_full_row_eventual_period
  no_uniform_centered_window_tail
  proved_unconditionally_no_uniform_centered_window_tail
  challenge_from_lift
  center_tail_window_lift_implies_center_column_nonperiodic
  center_column_nonperiodic_implies_not_purely_periodic
  center_tail_window_lift_implies_not_purely_periodic
  wolfram_form_from_lift
  reduction_contract_by_auto
  wolfram_form_by_auto.
