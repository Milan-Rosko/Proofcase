(*S003_01__Center_Normalization.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / S003_01__Center_Normalization                   │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file adds a period-defect normalization interface for the Rule 30
  center column. It does not prove center-column nonperiodicity. It proves
  that eventual periodicity is exactly the existence of a positive period
  whose defect normalizer reaches the terminal state `Omega`.

  The terminal state `Omega` is a normalization certificate, not logical
  absurdity: reaching `Omega` means that the proposed period has no defects
  from some cutoff onward. Productive nonperiodicity is exposed separately as
  a witness-producing statement.

*)

From S003 Require Export S003_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          PURE AND EVENTUAL PERIODS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A pure period is a positive period that works from time
│          zero.
│
*)

Definition center_pure_period (P : nat) : Prop :=
  (0 < P)%nat /\
  forall t,
    center_column (t + P)%nat = center_column t.

Lemma center_column_purely_periodic_iff_exists_pure_period :
  center_column_purely_periodic <->
  exists P, center_pure_period P.
Proof.
  unfold center_column_purely_periodic, center_pure_period.
  reflexivity.
Qed.

Lemma pure_period_is_tail_period :
  forall P,
    center_pure_period P ->
    center_tail_period 0 P.
Proof.
  intros P [HP Hperiod].
  unfold center_tail_period.
  split.
  - exact HP.
  - intros t _.
    exact (Hperiod t).
Qed.

Lemma pure_period_implies_eventually_periodic :
  center_column_purely_periodic ->
  center_column_eventually_periodic.
Proof.
  intros Hpure.
  apply center_column_purely_periodic_iff_exists_pure_period in Hpure.
  destruct Hpure as [P Hperiod].
  exists 0%nat, P.
  exact (pure_period_is_tail_period P Hperiod).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                PERIOD DEFECTS                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The `P`-defect stream records exactly where period `P`
│          fails.
│
*)

Definition period_defect (P t : nat) : bit :=
  xorb (center_column (t + P)%nat) (center_column t).

Definition is_period_defect (P t : nat) : Prop :=
  period_defect P t = true.

Definition defect_free_from (P N : nat) : Prop :=
  forall t,
    (N <= t)%nat ->
    period_defect P t = false.

Definition has_defect_from (P N : nat) : Prop :=
  exists t,
    (N <= t)%nat /\
    period_defect P t = true.

Lemma period_defect_false_iff_equal :
  forall P t,
    period_defect P t = false <->
    center_column (t + P)%nat = center_column t.
Proof.
  intros P t.
  unfold period_defect.
  destruct (center_column (t + P)%nat);
    destruct (center_column t);
    simpl;
    split;
    intro H;
    try reflexivity;
    try discriminate.
Qed.

Lemma period_defect_true_iff_neq :
  forall P t,
    period_defect P t = true <->
    center_column (t + P)%nat <> center_column t.
Proof.
  intros P t.
  unfold period_defect.
  destruct (center_column (t + P)%nat);
    destruct (center_column t);
    simpl;
    split;
    intro H;
    try discriminate;
    try congruence.
Qed.

Lemma defect_free_from_monotone :
  forall P N M,
    (N <= M)%nat ->
    defect_free_from P N ->
    defect_free_from P M.
Proof.
  intros P N M Hle Hfree t Ht.
  apply Hfree.
  lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         DEFECTS AND PURE PERIODICITY                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Lemma pure_period_iff_defect_free_from_zero :
  forall P,
    center_pure_period P <->
    (0 < P)%nat /\ defect_free_from P 0.
Proof.
  intro P.
  unfold center_pure_period, defect_free_from.
  split.
  - intros [HP Hperiod].
    split.
    + exact HP.
    + intros t _.
      apply period_defect_false_iff_equal.
      exact (Hperiod t).
  - intros [HP Hfree].
    split.
    + exact HP.
    + intro t.
      apply period_defect_false_iff_equal.
      apply Hfree.
      lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       DEFECTS AND EVENTUAL PERIODICITY                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Lemma tail_period_iff_defect_free_from :
  forall T P,
    center_tail_period T P <->
    (0 < P)%nat /\ defect_free_from P T.
Proof.
  intros T P.
  unfold center_tail_period, defect_free_from.
  split.
  - intros [HP Htail].
    split.
    + exact HP.
    + intros t Ht.
      apply period_defect_false_iff_equal.
      exact (Htail t Ht).
  - intros [HP Hfree].
    split.
    + exact HP.
    + intros t Ht.
      apply period_defect_false_iff_equal.
      exact (Hfree t Ht).
Qed.

Lemma eventually_periodic_iff_exists_defect_free_tail :
  center_column_eventually_periodic <->
  exists T P,
    (0 < P)%nat /\ defect_free_from P T.
Proof.
  unfold center_column_eventually_periodic.
  split.
  - intros [T [P Htail]].
    exists T, P.
    apply tail_period_iff_defect_free_from.
    exact Htail.
  - intros [T [P Hfree]].
    exists T, P.
    apply tail_period_iff_defect_free_from.
    exact Hfree.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              NORMALIZER STATES                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `Live N` continues the search for the next defect at or
│          after `N`; `Omega` certifies that no later defects remain.
│
*)

Inductive normalizer_state : Type :=
| Live : nat -> normalizer_state
| Omega : normalizer_state.

(*
│
│          `M` is the first `P`-defect at or after `N`.
│
*)

Definition next_defect_at (P N M : nat) : Prop :=
  (N <= M)%nat /\
  period_defect P M = true /\
  forall t,
    (N <= t)%nat ->
    (t < M)%nat ->
    period_defect P t = false.

Inductive period_normalizer_step (P : nat)
  : normalizer_state -> normalizer_state -> Prop :=
| step_to_next_defect :
    forall N M,
      next_defect_at P N M ->
      period_normalizer_step P (Live N) (Live (S M))
| step_to_omega :
    forall N,
      defect_free_from P N ->
      period_normalizer_step P (Live N) Omega
| step_omega_stable :
      period_normalizer_step P Omega Omega.

Lemma next_defect_step_strictly_increases :
  forall P N M,
    next_defect_at P N M ->
    (N < S M)%nat.
Proof.
  unfold next_defect_at.
  intros P N M [Hle _].
  lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 REACHABILITY                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Inductive normalizer_reaches (P : nat)
  : nat -> normalizer_state -> normalizer_state -> Prop :=
| reaches_zero :
    forall s,
      normalizer_reaches P 0 s s
| reaches_step :
    forall k s1 s2 s3,
      period_normalizer_step P s1 s2 ->
      normalizer_reaches P k s2 s3 ->
      normalizer_reaches P (S k) s1 s3.

Definition period_normalizes (P : nat) : Prop :=
  exists k,
    normalizer_reaches P k (Live 0) Omega.

Definition period_productive (P : nat) : Prop :=
  forall N,
    has_defect_from P N.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                     FINITE DEFECT SEARCH FOR TERMINATION                     │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The public normalizer is relational. This bounded search is
│          only a proof helper showing that a defect-free tail is
│          reached after finitely many jumps.
│
*)

Fixpoint first_defect_before (P N fuel : nat) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      if period_defect P N
      then Some N
      else first_defect_before P (S N) fuel'
  end.

Lemma first_defect_before_some :
  forall P N fuel M,
    first_defect_before P N fuel = Some M ->
    (N <= M)%nat /\
    (M < N + fuel)%nat /\
    period_defect P M = true /\
    forall t,
      (N <= t)%nat ->
      (t < M)%nat ->
      period_defect P t = false.
Proof.
  intros P N fuel.
  revert P N.
  induction fuel as [|fuel IH]; intros P N M Hfind.
  - simpl in Hfind.
    discriminate.
  - simpl in Hfind.
    destruct (period_defect P N) eqn:HN.
    + inversion Hfind; subst M; clear Hfind.
      split.
      * lia.
      * split.
        -- lia.
        -- split.
           ++ exact HN.
           ++ intros t Hle Hlt.
              exfalso.
              lia.
    + specialize (IH P (S N) M Hfind) as [Hle [Hlt [Hdef Hmin]]].
      split.
      * lia.
      * split.
        -- lia.
        -- split.
           ++ exact Hdef.
           ++ intros t HNt HtM.
              destruct (Nat.eq_dec t N) as [HtN | HtN].
              ** subst t.
                 exact HN.
              ** apply Hmin; lia.
Qed.

Lemma first_defect_before_none :
  forall P N fuel,
    first_defect_before P N fuel = None ->
    forall t,
      (N <= t)%nat ->
      (t < N + fuel)%nat ->
      period_defect P t = false.
Proof.
  intros P N fuel.
  revert P N.
  induction fuel as [|fuel IH]; intros P N Hfind t Hle Hlt.
  - simpl in Hfind.
    lia.
  - simpl in Hfind.
    destruct (period_defect P N) eqn:HN.
    + discriminate.
    + destruct (Nat.eq_dec t N) as [HtN | HtN].
      * subst t.
        exact HN.
      * eapply IH.
        -- exact Hfind.
        -- lia.
        -- lia.
Qed.

Lemma first_defect_before_some_next_defect_at :
  forall P N fuel M,
    first_defect_before P N fuel = Some M ->
    next_defect_at P N M.
Proof.
  intros P N fuel M Hfind.
  pose proof (first_defect_before_some P N fuel M Hfind)
    as [Hle [_ [Hdef Hmin]]].
  unfold next_defect_at.
  split.
  - exact Hle.
  - split.
    + exact Hdef.
    + exact Hmin.
Qed.

Lemma first_defect_before_none_tail_free :
  forall P N fuel T,
    first_defect_before P N fuel = None ->
    (T <= N + fuel)%nat ->
    defect_free_from P T ->
    defect_free_from P N.
Proof.
  intros P N fuel T Hfind Hbound Htail t HNt.
  destruct (lt_dec t (N + fuel)) as [Hlt | Hnlt].
  - eapply first_defect_before_none.
    + exact Hfind.
    + exact HNt.
    + exact Hlt.
  - apply Htail.
    lia.
Qed.

Lemma normalizer_reaches_omega_when_defect_free_from_bounded :
  forall fuel P N T,
    (T <= N + fuel)%nat ->
    defect_free_from P T ->
    exists k,
      normalizer_reaches P k (Live N) Omega.
Proof.
  intro fuel.
  induction fuel as [|fuel IH]; intros P N T Hbound Hfree.
  - assert (HTN : (T <= N)%nat) by lia.
    exists 1%nat.
    eapply reaches_step.
    + apply step_to_omega.
      eapply defect_free_from_monotone.
      * exact HTN.
      * exact Hfree.
    + apply reaches_zero.
  - destruct (le_lt_dec T N) as [HTN | HNT].
    + exists 1%nat.
      eapply reaches_step.
      * apply step_to_omega.
        eapply defect_free_from_monotone.
        -- exact HTN.
        -- exact Hfree.
      * apply reaches_zero.
    + destruct (first_defect_before P N (S fuel)) eqn:Hfind.
      * pose proof
          (first_defect_before_some_next_defect_at P N (S fuel) n Hfind)
          as Hnext.
        pose proof Hnext as [HNn _].
        assert (Hbound' : (T <= S n + fuel)%nat) by lia.
        destruct (IH P (S n) T Hbound' Hfree) as [k Hreach].
        exists (S k).
        eapply reaches_step.
        -- apply step_to_next_defect.
           exact Hnext.
        -- exact Hreach.
      * pose proof
          (first_defect_before_none_tail_free
             P N (S fuel) T Hfind Hbound Hfree)
          as HfreeN.
        exists 1%nat.
        eapply reaches_step.
        -- apply step_to_omega.
           exact HfreeN.
        -- apply reaches_zero.
Qed.

Lemma normalizer_reaches_omega_when_defect_free_from :
  forall P T,
    defect_free_from P T ->
    exists k,
      normalizer_reaches P k (Live 0) Omega.
Proof.
  intros P T Hfree.
  apply (normalizer_reaches_omega_when_defect_free_from_bounded T P 0 T).
  - lia.
  - exact Hfree.
Qed.

Lemma normalizer_reaches_live_to_omega_defect_free :
  forall P k N,
    normalizer_reaches P k (Live N) Omega ->
    exists T,
      defect_free_from P T.
Proof.
  intros P k.
  induction k as [|k IH]; intros N Hreach.
  - inversion Hreach.
  - inversion Hreach as [|? s1 s2 s3 Hstep Htail]; subst.
    inversion Hstep as [Nstart M Hnext | Ncut Hfree |]; subst.
    + eapply IH.
      exact Htail.
    + exists N.
      exact Hfree.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                    NORMALIZATION AND EVENTUAL PERIODICITY                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Theorem period_normalizes_implies_eventual_period :
  forall P,
    (0 < P)%nat ->
    period_normalizes P ->
    exists T,
      center_tail_period T P.
Proof.
  intros P HP [k Hreach].
  destruct
    (normalizer_reaches_live_to_omega_defect_free P k 0 Hreach)
    as [T Hfree].
  exists T.
  apply tail_period_iff_defect_free_from.
  split.
  - exact HP.
  - exact Hfree.
Qed.

Theorem eventual_period_implies_period_normalizes :
  forall T P,
    center_tail_period T P ->
    period_normalizes P.
Proof.
  intros T P Htail.
  apply tail_period_iff_defect_free_from in Htail.
  destruct Htail as [_ Hfree].
  unfold period_normalizes.
  exact (normalizer_reaches_omega_when_defect_free_from P T Hfree).
Qed.

Theorem period_normalizes_iff_eventual_period :
  forall P,
    (0 < P)%nat ->
    period_normalizes P <->
    exists T, center_tail_period T P.
Proof.
  intros P HP.
  split.
  - apply period_normalizes_implies_eventual_period.
    exact HP.
  - intros [T Htail].
    exact (eventual_period_implies_period_normalizes T P Htail).
Qed.

Theorem center_eventually_periodic_iff_some_period_normalizes :
  center_column_eventually_periodic <->
  exists P,
    (0 < P)%nat /\ period_normalizes P.
Proof.
  unfold center_column_eventually_periodic.
  split.
  - intros [T [P Htail]].
    destruct Htail as [HP Htail].
    exists P.
    split.
    + exact HP.
    + apply eventual_period_implies_period_normalizes with (T := T).
      split.
      * exact HP.
      * exact Htail.
  - intros [P [HP Hnorm]].
    destruct
      (period_normalizes_implies_eventual_period P HP Hnorm)
      as [T Htail].
    exists T, P.
    exact Htail.
Qed.

Definition CENTER_NORMALIZATION_INTERFACE : Prop :=
  center_column_eventually_periodic <->
  exists P,
    (0 < P)%nat /\ period_normalizes P.

Theorem certified_center_normalization_interface :
  CENTER_NORMALIZATION_INTERFACE.
Proof.
  exact center_eventually_periodic_iff_some_period_normalizes.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         CONSTRUCTIVE NONPERIODICITY                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition CENTER_COLUMN_PRODUCTIVELY_NONPERIODIC : Prop :=
  forall P N,
    (0 < P)%nat ->
    has_defect_from P N.

Theorem productive_nonperiodic_implies_center_nonperiodic :
  CENTER_COLUMN_PRODUCTIVELY_NONPERIODIC ->
  CENTER_COLUMN_NONPERIODIC.
Proof.
  unfold CENTER_COLUMN_PRODUCTIVELY_NONPERIODIC,
    CENTER_COLUMN_NONPERIODIC,
    center_column_eventually_periodic.
  intros Hproductive [T [P Htail]].
  apply tail_period_iff_defect_free_from in Htail.
  destruct Htail as [HP Hfree].
  destruct (Hproductive P T HP) as [t [Ht Hdef]].
  pose proof (Hfree t Ht) as Hnodef.
  rewrite Hnodef in Hdef.
  discriminate.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                     PURE VERSUS EVENTUAL NONPERIODICITY                      │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition center_not_purely_periodic_productive : Prop :=
  forall P,
    (0 < P)%nat ->
    has_defect_from P 0.

Theorem productive_eventual_nonperiodic_implies_productive_not_pure :
  CENTER_COLUMN_PRODUCTIVELY_NONPERIODIC ->
  center_not_purely_periodic_productive.
Proof.
  intros Hproductive P HP.
  exact (Hproductive P 0 HP).
Qed.

Theorem productive_not_pure_implies_not_purely_periodic :
  center_not_purely_periodic_productive ->
  CENTER_COLUMN_NOT_PURELY_PERIODIC.
Proof.
  unfold center_not_purely_periodic_productive,
    CENTER_COLUMN_NOT_PURELY_PERIODIC,
    center_column_purely_periodic.
  intros Hproductive [P [HP Hperiod]].
  destruct (Hproductive P HP) as [t [_ Hdef]].
  apply period_defect_true_iff_neq in Hdef.
  apply Hdef.
  exact (Hperiod t).
Qed.

(*
│
│          The converse from negated eventual periodicity to
│          productive nonperiodicity is intentionally absent.
│          Constructively, `~ exists T, defect_free_from P T` does not
│          by itself produce, for every cutoff `N`, a concrete later
│          defect.
│
*)
