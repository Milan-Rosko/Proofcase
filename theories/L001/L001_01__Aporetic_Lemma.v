(*L001_01__Aporetic_Lemma.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / L001_01__Aporetic_Lemma                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  The goal-restricted diagonal theorem and the local collapse hierarchy. The
  branchwise theorem names exactly three detachment instances; global modus
  ponens supplies them for the goal-relative theorem, whose bottom
  specialization is the retained local-collapse contract.

*)

From L001 Require Export L001_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              NEGATION DIAGONAL                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Specializing the supplied code at itself produces a formula
│          closure-equivalent to its own negation.
│
*)

Theorem eval_bottom_negfixp :
  forall (C : Formula -> Prop) Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal C Code ev Bot ->
    exists B : Formula,
      NegationFixedPointFor C B.
Proof.
  intros C Code ev [c Hc].
  exists (ev c c).
  exact (Hc c).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                LOCAL COLLAPSE                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          For an arbitrary goal `G`, each accepted branch needs only
│          the fixed-point implication oriented from that branch, one
│          branch-specific detachment instance, and the shared final
│          detachment from `B` to `G`.
│
*)

Theorem branchwise_goal_relative_collapse :
  forall (C : Formula -> Prop) B G,
    ClosureDetachmentAt C B (Imp B G) ->
    ClosureDetachmentAt C (Imp B G) B ->
    ClosureDetachmentAt C B G ->
    ((C B /\ C (Imp B (Imp B G))) \/
     (C (Imp B G) /\ C (Imp (Imp B G) B))) ->
    C G.
Proof.
  intros C B G Hforward_det Hbackward_det Hfinal Hbranch.
  destruct Hbranch as [[HB Hforward] | [HBG Hbackward]].
  - pose proof (Hforward_det Hforward HB) as HBG.
    exact (Hfinal HBG HB).
  - pose proof (Hbackward_det Hbackward HBG) as HB.
    exact (Hfinal HBG HB).
Qed.

(*
│
│          Full closure equivalence and global modus ponens supply the
│          branchwise theorem's oriented implications and three local
│          detachment instances.
│
*)

Theorem goal_relative_branch_collapse :
  forall (C : Formula -> Prop) B G,
    ClosureModusPonens C ->
    ClosureEquiv C B (Imp B G) ->
    (C B \/ C (Imp B G)) ->
    C G.
Proof.
  intros C B G Hmp [Hforward Hbackward] [HB | HBG].
  - apply
      (branchwise_goal_relative_collapse
        C B G
        (closure_modus_ponens_detachment_at C B (Imp B G) Hmp)
        (closure_modus_ponens_detachment_at C (Imp B G) B Hmp)
        (closure_modus_ponens_detachment_at C B G Hmp)).
    left.
    split; assumption.
  - apply
      (branchwise_goal_relative_collapse
        C B G
        (closure_modus_ponens_detachment_at C B (Imp B G) Hmp)
        (closure_modus_ponens_detachment_at C (Imp B G) B Hmp)
        (closure_modus_ponens_detachment_at C B G Hmp)).
    right.
    split; assumption.
Qed.

(*
│
│          Negation is implication to `Bot`, so the retained local
│          branch collapse is the bottom specialization of the
│          goal-relative theorem.
│
*)

Theorem local_branch_collapse :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    ClosureLocalExcludedMiddle C B ->
    C Bot.
Proof.
  intros C B Hmp Hfixed Hlocal.
  unfold NegationFixedPointFor,
    ClosureLocalExcludedMiddle,
    formula_negation in *.
  exact (goal_relative_branch_collapse C B Bot Hmp Hfixed Hlocal).
Qed.
