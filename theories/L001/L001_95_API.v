(*L001_95_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / L001_95_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  The six canonical L001 contracts together with the derived goal-relative,
  branchwise, local-detachment, and fixed-point-gap endpoints. The
  strengthenings remain ordinary public theorems and do not enlarge the
  aggregate contract. This API contains no legacy contract names, full-frame
  wrappers, regulator restatements, or duplicate decision surfaces.

*)

From L001 Require Export L001_02__Aporetic_Obstruction.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              DERIVED ENDPOINTS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The cumulative export above exposes `closure_modus_ponens_detachment_at`,
  `branchwise_goal_relative_collapse`, `goal_relative_branch_collapse`, and
  `fixedpoint_gap`. They refine the local-collapse dependency boundary
  without adding clauses to `L001_CONTRACT`.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              PUBLIC VOCABULARY                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A closure theory is only a formula-indexed proposition.
│
*)

Definition ClosureTheory : Type := Formula -> Prop.

Definition ClosureNegationFixedPoint
    (C : ClosureTheory)
    (B : Formula) : Prop :=
  NegationFixedPointFor C B.

Definition ClosureLocalLEM
    (C : ClosureTheory)
    (B : Formula) : Prop :=
  ClosureLocalExcludedMiddle C B.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                  CONTRACTS                                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The local branch and fixed-point data collapse to accepted
│          bottom.
│
*)

Definition LOCAL_COLLAPSE : Prop :=
  forall (C : ClosureTheory) (B : Formula),
    ClosureModusPonens C ->
    ClosureNegationFixedPoint C B ->
    ClosureLocalLEM C B ->
    C Bot.

(*
│
│          Consistency turns the local collapse into contradiction.
│
*)

Definition LOCAL_OBSTRUCTION : Prop :=
  forall (C : ClosureTheory) (B : Formula),
    ClosureModusPonens C ->
    ClosureConsistent C ->
    ClosureNegationFixedPoint C B ->
    ClosureLocalLEM C B ->
    False.

(*
│
│          The bottom goal frame supplies the required negation fixed
│          point.
│
*)

Definition NEGATION_DIAGONAL : Prop :=
  forall (C : ClosureTheory) Code
         (ev : Code -> Code -> Formula),
    ClosureEvaluationFrameForGoal C Code ev Bot ->
    exists B : Formula,
      ClosureNegationFixedPoint C B.

(*
│
│          A signed classifier is incompatible with a consistent
│          closure at a supplied negation fixed point.
│
*)

Definition SIGNED_OBSTRUCTION : Prop :=
  forall (C : ClosureTheory) (B : Formula),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureNegationFixedPoint C B ->
    ClosureSignedClassification C ->
    False.

(*
│
│          The corresponding membership obstruction keeps refutation
│          completeness explicit.
│
*)

Definition MEMBERSHIP_OBSTRUCTION : Prop :=
  forall (C : ClosureTheory) (B : Formula),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureNegationFixedPoint C B ->
    ClosureRefutationComplete C ->
    ClosureMembershipDecision C ->
    False.

(*
│
│          Negative-only refutation remains inhabited unconditionally.
│
*)

Definition REFUTATION_INHABITED : Prop :=
  forall C : ClosureTheory,
    exists r : Formula -> bool,
      (forall A, r A = false) /\
      (forall A, r A = true -> C (formula_negation A)).

(*
│
│          The aggregate contains the six contracts in proof order.
│
*)

Definition L001_CONTRACT : Prop :=
  LOCAL_COLLAPSE /\
  LOCAL_OBSTRUCTION /\
  NEGATION_DIAGONAL /\
  SIGNED_OBSTRUCTION /\
  MEMBERSHIP_OBSTRUCTION /\
  REFUTATION_INHABITED.
