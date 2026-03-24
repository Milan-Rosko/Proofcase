(* R02__Progenitor_Obstruction.v *)

From Coq Require Import Arith Bool Lia List ZArith.
Import ListNotations.

From T004 Require Import
  R01__Cellular_Semantics.

Open Scope Z_scope.
Set Bullet Behavior "None".

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / T004 -- Progenitor Obstruction                           *)
(*                                                                       *)
(*  This layer isolates the constructive contradiction core of T004:     *)
(*  the single-seed row has no finitely supported progenitor, and        *)
(*  support-covering replay collapses to that same forbidden witness.    *)
(*                                                                       *)
(*************************************************************************)

Section Progenitor_Obstruction.

(*
  Canonical documentation for `Progenitor`.
*)

Definition Progenitor (u v : row) : Prop :=
  exists N,
    supported_in N u /\
    (forall x, v x = step_of Rule30 u x).

(*
  Canonical documentation for `boundary_forcing_on_seed_predecessor`.
*)

Lemma boundary_forcing_on_seed_predecessor :
  forall u N,
    supported_in N u ->
    (forall x, seed_row x = step_of Rule30 u x) ->
    forall k,
      (k <= S N)%nat ->
      u (Z.of_nat k - Z.of_nat N - 2)%Z = false /\
      u (Z.of_nat k - Z.of_nat N - 1)%Z = false.
Proof.
  intros u N Hsupp Hstep.
  induction k as [|k IH]; intro Hk.
  - split.
    + apply Hsupp. lia.
    + apply Hsupp. lia.
  - assert (HkSN : (k <= S N)%nat) by lia.
    specialize (IH HkSN).
    destruct IH as [Hleft Hmid].
    split.
    + replace (Z.of_nat (S k) - Z.of_nat N - 2)%Z
        with (Z.of_nat k - Z.of_nat N - 1)%Z by lia.
      exact Hmid.
    + replace (Z.of_nat (S k) - Z.of_nat N - 1)%Z
        with (Z.of_nat k - Z.of_nat N)%Z by lia.
      specialize (Hstep (Z.of_nat k - Z.of_nat N - 1)%Z).
      assert (Hseed_zero : seed_row (Z.of_nat k - Z.of_nat N - 1)%Z = false).
      - unfold seed_row.
        apply Z.eqb_neq.
        lia.
      rewrite Hseed_zero in Hstep.
      unfold step_of in Hstep.
      replace (Z.of_nat k - Z.of_nat N - 1 - 1)%Z
        with (Z.of_nat k - Z.of_nat N - 2)%Z in Hstep by lia.
      replace (Z.of_nat k - Z.of_nat N - 1 + 1)%Z
        with (Z.of_nat k - Z.of_nat N)%Z in Hstep by lia.
      rewrite Hleft, Hmid in Hstep.
      symmetry in Hstep.
      rewrite Rule30_00c in Hstep.
      exact Hstep.
Qed.

(*
  Canonical documentation for `local_contradiction_at_origin_and_adjacent_site`.
*)

Lemma local_contradiction_at_origin_and_adjacent_site :
  forall u,
    u (-1)%Z = false ->
    u 0%Z = false ->
    Rule30 (u (-1)%Z) (u 0%Z) (u 1%Z) = true ->
    Rule30 (u 0%Z) (u 1%Z) (u 2%Z) = false ->
    False.
Proof.
  intros u Hm1 H0 Horig Hadj.
  rewrite Hm1, H0 in Horig.
  rewrite Rule30_00c in Horig.
  assert (Hu1 : u 1%Z = true) by exact Horig.
  rewrite H0, Hu1 in Hadj.
  rewrite Rule30_01c_true in Hadj.
  discriminate Hadj.
Qed.

(*
  Canonical documentation for `No_Progenitor_Theorem`.
*)

Theorem No_Progenitor_Theorem :
  forall u,
    ~ Progenitor u seed_row.
Proof.
  intros u Hprog.
  destruct Hprog as [N [Hsupp Himg]].
  pose proof
    (boundary_forcing_on_seed_predecessor u N Hsupp Himg (S N)
       (Nat.le_refl (S N))) as Hpair.
  destruct Hpair as [Hm1 H0].
  replace (Z.of_nat (S N) - Z.of_nat N - 2)%Z with (-1)%Z in Hm1 by lia.
  replace (Z.of_nat (S N) - Z.of_nat N - 1)%Z with 0%Z in H0 by lia.
  assert (Horig : Rule30 (u (-1)%Z) (u 0%Z) (u 1%Z) = true).
  - specialize (Himg 0%Z).
    unfold step_of in Himg.
    unfold seed_row in Himg.
    replace (0 - 1)%Z with (-1)%Z in Himg by lia.
    replace (0 + 1)%Z with 1%Z in Himg by lia.
    simpl in Himg.
    symmetry.
    exact Himg.
  assert (Hadj : Rule30 (u 0%Z) (u 1%Z) (u 2%Z) = false).
  - specialize (Himg 1%Z).
    unfold step_of in Himg.
    unfold seed_row in Himg.
    replace (1 - 1)%Z with 0%Z in Himg by lia.
    replace (1 + 1)%Z with 2%Z in Himg by lia.
    simpl in Himg.
    symmetry.
    exact Himg.
  eapply local_contradiction_at_origin_and_adjacent_site.
  - exact Hm1.
  - exact H0.
  - exact Horig.
  - exact Hadj.
Qed.

(*
  Backward-compatible obstruction aliases.
*)

Definition Ex_Nihilo_Obstruction := No_Progenitor_Theorem.
Definition no_progenitor_theorem := No_Progenitor_Theorem.

(*
  Canonical documentation for `seed_not_created_from_finite_support`.
*)

Corollary seed_not_created_from_finite_support :
  ~ (exists u, Progenitor u seed_row).
Proof.
  intro Hex.
  destruct Hex as [u Hu].
  exact (No_Progenitor_Theorem u Hu).
Qed.

(*************************************************************************)
(*                                                                       *)
(*  THEOREM BOX -- support_covering_centered_line_replay_impossible      *)
(*                                                                       *)
(*************************************************************************)

(*
  PROOF ROUTE
  (1) Assume support-covering replay for period `P`.
  (2) Convert the replay equality into full-row equality at time `P`.
  (3) Build a progenitor witness for `seed_row` from row `P - 1`.
  (4) Contradict `No_Progenitor_Theorem`.
*)

Theorem support_covering_centered_line_replay_impossible :
  forall n P,
    (0 < P <= n)%nat ->
    ~ (forall t,
        canonical_centered_line n (t + P)%nat =
        canonical_centered_line n t).
Proof.
  intros n [|p] HP Hreplay.
  - lia.
  - assert (Hpn : (S p <= n)%nat) by lia.
    pose proof (Hreplay 0%nat) as H0.
    assert (Hseedrow : forall x, Rule30_row (S p) x = seed_row x).
    - intro x.
      destruct (Z_le_dec (- Z.of_nat n) x) as [Hlo|Hlo];
      destruct (Z_le_dec x (Z.of_nat n)) as [Hhi|Hhi].
      + transitivity (Rule30_row 0%nat x).
        * eapply (@centered_window_eq_pointwise
                    (Rule30_row (S p))
                    (Rule30_row 0%nat)
                    n x).
          -- lia.
          -- exact H0.
        * apply Rule30_row_zero_eq_seed.
      + assert (Hout : (x < - Z.of_nat (S p) \/ Z.of_nat (S p) < x)%Z) by lia.
        transitivity false.
        * apply (Rule30_supported (S p)).
          exact Hout.
        * symmetry.
          unfold seed_row.
          apply Z.eqb_neq.
          lia.
      + assert (Hout : (x < - Z.of_nat (S p) \/ Z.of_nat (S p) < x)%Z) by lia.
        transitivity false.
        * apply (Rule30_supported (S p)).
          exact Hout.
        * symmetry.
          unfold seed_row.
          apply Z.eqb_neq.
          lia.
      + exfalso.
        lia.
    assert (Hprog : Progenitor (Rule30_row p) seed_row).
    - exists p.
      split.
      + apply Rule30_supported.
      + intro x.
        rewrite <- (Hseedrow x).
        symmetry.
        apply Rule30_row_successor.
    exact (no_progenitor_theorem (Rule30_row p) Hprog).
Qed.

(*
  Canonical documentation for
  `support_covering_centered_line_single_replay_at_zero_impossible`.
*)

Theorem support_covering_centered_line_single_replay_at_zero_impossible :
  forall n P,
    (0 < P <= n)%nat ->
    canonical_centered_line n P = canonical_centered_line n 0%nat ->
    False.
Proof.
  intros n [|p] HP H0.
  - lia.
  - assert (Hpn : (S p <= n)%nat) by lia.
    assert (Hseedrow : forall x, Rule30_row (S p) x = seed_row x).
    - intro x.
      destruct (Z_le_dec (- Z.of_nat n) x) as [Hlo|Hlo];
      destruct (Z_le_dec x (Z.of_nat n)) as [Hhi|Hhi].
      + transitivity (Rule30_row 0%nat x).
        * eapply (@centered_window_eq_pointwise
                    (Rule30_row (S p))
                    (Rule30_row 0%nat)
                    n x).
          -- lia.
          -- exact H0.
        * apply Rule30_row_zero_eq_seed.
      + assert (Hout : (x < - Z.of_nat (S p) \/ Z.of_nat (S p) < x)%Z) by lia.
        transitivity false.
        * apply (Rule30_supported (S p)).
          exact Hout.
        * symmetry.
          unfold seed_row.
          apply Z.eqb_neq.
          lia.
      + assert (Hout : (x < - Z.of_nat (S p) \/ Z.of_nat (S p) < x)%Z) by lia.
        transitivity false.
        * apply (Rule30_supported (S p)).
          exact Hout.
        * symmetry.
          unfold seed_row.
          apply Z.eqb_neq.
          lia.
      + exfalso.
        lia.
    assert (Hprog : Progenitor (Rule30_row p) seed_row).
    - exists p.
      split.
      + apply Rule30_supported.
      + intro x.
        rewrite <- (Hseedrow x).
        symmetry.
        apply Rule30_row_successor.
    exact (no_progenitor_theorem (Rule30_row p) Hprog).
Qed.

End Progenitor_Obstruction.

Global Opaque
  boundary_forcing_on_seed_predecessor
  local_contradiction_at_origin_and_adjacent_site
  No_Progenitor_Theorem
  Ex_Nihilo_Obstruction
  no_progenitor_theorem
  seed_not_created_from_finite_support
  support_covering_centered_line_replay_impossible
  support_covering_centered_line_single_replay_at_zero_impossible.
