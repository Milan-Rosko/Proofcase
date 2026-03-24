(* R06__No_Tamper_Checker.v *)

From Coq Require Import Bool Lia ZArith.

From T004 Require Import R01__Cellular_Semantics.

Open Scope Z_scope.
Set Bullet Behavior "None".

(*************************************************************************)
(*                                                                       *)
(*  Layer 1: Rule 30 Algebraic Structure                                 *)
(*                                                                       *)
(*************************************************************************)

Lemma Rule30_xorb_orb :
  forall a b c,
    Rule30 a b c = xorb a (orb b c).
Proof.
  intros [] [] []; reflexivity.
Qed.

Lemma Rule30_left_inverse :
  forall o b c,
    Rule30 (xorb o (orb b c)) b c = o.
Proof.
  intros o b c.
  rewrite Rule30_xorb_orb.
  destruct o, b, c; reflexivity.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 2: Reverse Carrier Reconstruction                              *)
(*                                                                       *)
(*************************************************************************)

Definition reverse_carrier (obs : row) (R : nat) (w : row) : Prop :=
  forall x,
    (- Z.of_nat R <= x <= Z.of_nat R)%Z ->
    step_of Rule30 w x = obs x.

Fixpoint carrier_step
  (obs : row) (R : nat) (b c : bool) (n : nat)
  : bool * bool :=
  match n with
  | O => (b, c)
  | S m =>
      let '(vm1, vm) := carrier_step obs R b c m in
      (xorb (obs (Z.of_nat R - Z.of_nat m)%Z) (orb vm1 vm), vm1)
  end.

Definition carrier_val
  (obs : row) (R : nat) (b c : bool) (i : nat) : bool :=
  snd (carrier_step obs R b c i).

Definition reconstructed_row
  (obs : row) (R : nat) (b c : bool) : row :=
  fun x => carrier_val obs R b c (Z.to_nat (Z.of_nat R + 1 - x)).

Lemma carrier_val_0 :
  forall obs R b c,
    carrier_val obs R b c 0 = c.
Proof.
  reflexivity.
Qed.

Lemma carrier_val_1 :
  forall obs R b c,
    carrier_val obs R b c 1 = b.
Proof.
  reflexivity.
Qed.

Lemma carrier_val_step :
  forall obs R b c n,
    carrier_val obs R b c (S (S n)) =
    xorb (obs (Z.of_nat R - Z.of_nat n)%Z)
         (orb (carrier_val obs R b c (S n))
              (carrier_val obs R b c n)).
Proof.
  intros obs R b c n.
  unfold carrier_val.
  simpl.
  destruct (carrier_step obs R b c n) as [vm1 vm].
  reflexivity.
Qed.

Lemma reconstructed_row_at_index :
  forall obs R b c i,
    reconstructed_row obs R b c (Z.of_nat R + 1 - Z.of_nat i)%Z =
    carrier_val obs R b c i.
Proof.
  intros obs R b c i.
  unfold reconstructed_row.
  replace (Z.of_nat R + 1 - (Z.of_nat R + 1 - Z.of_nat i))%Z
    with (Z.of_nat i)%Z by lia.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 3: Validity of Reconstruction                                  *)
(*                                                                       *)
(*************************************************************************)

Theorem reconstructed_row_valid :
  forall obs R b c,
    reverse_carrier obs R (reconstructed_row obs R b c).
Proof.
  intros obs R b c x Hx.
  set (n := Z.to_nat (Z.of_nat R - x)).
  assert (Hn : (Z.of_nat n = Z.of_nat R - x)%Z).
  { unfold n. apply Z2Nat.id. lia. }
  assert (Hxeq : x = (Z.of_nat R - Z.of_nat n)%Z) by lia.
  rewrite Hxeq.
  unfold step_of.
  assert (Hleft :
    reconstructed_row obs R b c (Z.of_nat R - Z.of_nat n - 1) =
    carrier_val obs R b c (S (S n))).
  {
    replace (Z.of_nat R - Z.of_nat n - 1)%Z
      with (Z.of_nat R + 1 - Z.of_nat (S (S n)))%Z by lia.
    apply reconstructed_row_at_index.
  }
  assert (Hmid :
    reconstructed_row obs R b c (Z.of_nat R - Z.of_nat n) =
    carrier_val obs R b c (S n)).
  {
    replace (Z.of_nat R - Z.of_nat n)%Z
      with (Z.of_nat R + 1 - Z.of_nat (S n))%Z by lia.
    apply reconstructed_row_at_index.
  }
  assert (Hright :
    reconstructed_row obs R b c (Z.of_nat R - Z.of_nat n + 1) =
    carrier_val obs R b c n).
  {
    replace (Z.of_nat R - Z.of_nat n + 1)%Z
      with (Z.of_nat R + 1 - Z.of_nat n)%Z by lia.
    apply reconstructed_row_at_index.
  }
  rewrite Hleft, Hmid, Hright.
  rewrite carrier_val_step.
  apply Rule30_left_inverse.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 4: Boundary Injectivity                                        *)
(*                                                                       *)
(*************************************************************************)

Lemma reconstructed_row_at_R :
  forall obs R b c,
    reconstructed_row obs R b c (Z.of_nat R) = b.
Proof.
  intros obs R b c.
  replace (Z.of_nat R)%Z with (Z.of_nat R + 1 - Z.of_nat 1)%Z by lia.
  rewrite reconstructed_row_at_index.
  apply carrier_val_1.
Qed.

Lemma reconstructed_row_at_Rplus1 :
  forall obs R b c,
    reconstructed_row obs R b c (Z.of_nat R + 1) = c.
Proof.
  intros obs R b c.
  replace (Z.of_nat R + 1)%Z with (Z.of_nat R + 1 - Z.of_nat 0)%Z by lia.
  rewrite reconstructed_row_at_index.
  apply carrier_val_0.
Qed.

Theorem boundary_injective :
  forall obs R b1 c1 b2 c2,
    (b1, c1) <> (b2, c2) ->
    reconstructed_row obs R b1 c1 <> reconstructed_row obs R b2 c2.
Proof.
  intros obs R b1 c1 b2 c2 Hneq Heq.
  apply Hneq.
  assert (Hb : b1 = b2).
  {
    pose proof (f_equal (fun r => r (Z.of_nat R)) Heq) as H.
    change
      (reconstructed_row obs R b1 c1 (Z.of_nat R) =
       reconstructed_row obs R b2 c2 (Z.of_nat R)) in H.
    rewrite (reconstructed_row_at_R obs R b1 c1) in H.
    rewrite (reconstructed_row_at_R obs R b2 c2) in H.
    exact H.
  }
  assert (Hc : c1 = c2).
  {
    pose proof (f_equal (fun r => r (Z.of_nat R + 1)) Heq) as H.
    change
      (reconstructed_row obs R b1 c1 (Z.of_nat R + 1) =
       reconstructed_row obs R b2 c2 (Z.of_nat R + 1)) in H.
    rewrite (reconstructed_row_at_Rplus1 obs R b1 c1) in H.
    rewrite (reconstructed_row_at_Rplus1 obs R b2 c2) in H.
    exact H.
  }
  subst.
  reflexivity.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 5: Canonical Carrier and Alternative                           *)
(*                                                                       *)
(*************************************************************************)

Lemma canonical_is_reverse_carrier :
  forall R T,
    reverse_carrier (Rule30_row (S T)) R (Rule30_row T).
Proof.
  intros R T x _.
  symmetry.
  apply canonical_row_step.
Qed.

Theorem alternative_carrier_exists :
  forall R T,
    exists w : row,
      reverse_carrier (Rule30_row (S T)) R w /\
      w <> Rule30_row T.
Proof.
  intros R T.
  set (b := Rule30_row T (Z.of_nat R)).
  set (c := Rule30_row T (Z.of_nat R + 1)).
  exists (reconstructed_row (Rule30_row (S T)) R (negb b) c).
  split.
  - apply reconstructed_row_valid.
  - intro Heq.
    pose proof (f_equal (fun r => r (Z.of_nat R)) Heq) as H.
    change
      (reconstructed_row (Rule30_row (S T)) R (negb b) c (Z.of_nat R) =
       Rule30_row T (Z.of_nat R)) in H.
    rewrite (reconstructed_row_at_R (Rule30_row (S T)) R (negb b) c) in H.
    unfold b in H.
    destruct (Rule30_row T (Z.of_nat R)); discriminate.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Layer 6: No Tamper Checker                                           *)
(*                                                                       *)
(*************************************************************************)

Definition tamper_checker_at (R T : nat) (Theta : row -> bool) : Prop :=
  let obs := Rule30_row (S T) in
  Theta obs = false /\
  forall w,
    reverse_carrier obs R w ->
    w <> Rule30_row T ->
    Theta obs = true.

Theorem No_Tamper_Checker :
  forall R T Theta,
    ~ tamper_checker_at R T Theta.
Proof.
  intros R T Theta [Hfalse Htrue].
  destruct (alternative_carrier_exists R T) as [w [Hcarrier Hneq]].
  specialize (Htrue w Hcarrier Hneq).
  rewrite Hfalse in Htrue.
  discriminate Htrue.
Qed.

Global Opaque
  Rule30_xorb_orb
  Rule30_left_inverse
  reconstructed_row_valid
  boundary_injective
  canonical_is_reverse_carrier
  alternative_carrier_exists
  No_Tamper_Checker.
