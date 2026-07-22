(*L001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / L001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Minimal vocabulary for the six L001 contracts and their derived
  strengthenings: closure-level mutual implication, global and local
  detachment, consistency, local bivalence, signed and membership
  classification, and goal-restricted diagonal production.

*)

From M001 Require Export M001_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   CLOSURE                                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `ClosureEquiv C A B` contains exactly two accepted
│          implications. It supplies no equality, substitution,
│          congruence, or transitivity law.
│
*)

Definition ClosureEquiv
    (C : Formula -> Prop)
    (A B : Formula) : Prop :=
  C (Imp A B) /\ C (Imp B A).

(*
│
│          Modus ponens is the only closure rule used by the collapse.
│          It acts on top-level `C` facts and does not introduce or
│          discharge assumptions.
│
*)

Definition ClosureModusPonens
    (C : Formula -> Prop) : Prop :=
  forall A B,
    C (Imp A B) ->
    C A ->
    C B.

(*
│
│          `ClosureDetachmentAt C A D` is one named instance of
│          closure modus ponens. The branchwise goal-relative collapse
│          states only the three instances it uses; global
│          `ClosureModusPonens C` supplies each of them.
│
*)

Definition ClosureDetachmentAt
    (C : Formula -> Prop)
    (A D : Formula) : Prop :=
  C (Imp A D) ->
  C A ->
  C D.

Lemma closure_modus_ponens_detachment_at :
  forall C A D,
    ClosureModusPonens C ->
    ClosureDetachmentAt C A D.
Proof.
  intros C A D Hmp.
  exact (Hmp A D).
Qed.

(*
│
│          Consistency is an external guard: an accepted object-level
│          bottom formula contradicts the ambient Rocq context.
│
*)

Definition ClosureConsistent
    (C : Formula -> Prop) : Prop :=
  C Bot -> False.

(*
│
│          A negation fixed point is mutual accepted implication
│          between `B` and `B -> Bot`; it is not a syntactic identity.
│
*)

Definition NegationFixedPointFor
    (C : Formula -> Prop)
    (B : Formula) : Prop :=
  ClosureEquiv C B (formula_negation B).

(*
│
│          Local excluded middle is the single branch required at the
│          fixed formula. The disjunction lives in Rocq, not in the
│          object language.
│
*)

Definition ClosureLocalExcludedMiddle
    (C : Formula -> Prop)
    (B : Formula) : Prop :=
  C B \/ C (formula_negation B).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                CLASSIFICATION                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A signed classifier certifies acceptance of `A` on `true`
│          and acceptance of its object-language negation on `false`.
│
*)

Record ClosureSignedClassification
    (C : Formula -> Prop) : Type := {
  signed_classify : Formula -> bool;

  signed_true :
    forall A,
      signed_classify A = true ->
      C A;

  signed_false :
    forall A,
      signed_classify A = false ->
      C (formula_negation A)
}.

Arguments signed_classify {C} _ _.
Arguments signed_true {C} _ _ _.
Arguments signed_false {C} _ _ _.

(*
│
│          A membership decision specifies Boolean membership in `C`.
│          Its false result supplies non-membership, not an accepted
│          negation.
│
*)

Record ClosureMembershipDecision
    (C : Formula -> Prop) : Type := {
  membership_decide : Formula -> bool;

  membership_spec :
    forall A,
      membership_decide A = true <-> C A
}.

Arguments membership_decide {C} _ _.
Arguments membership_spec {C} _ _.

(*
│
│          Refutation completeness is the additional bridge from
│          external non-membership to internal acceptance of the
│          negated formula.
│
*)

Definition ClosureRefutationComplete
    (C : Formula -> Prop) : Prop :=
  forall A,
    ~ C A ->
    C (formula_negation A).

(*
│
│          With that bridge, the same Boolean membership function
│          becomes a signed classifier.
│
*)

Theorem membership_to_signed :
  forall C,
    ClosureRefutationComplete C ->
    ClosureMembershipDecision C ->
    ClosureSignedClassification C.
Proof.
  intros C Hrefutation D.
  refine
    {| signed_classify := membership_decide D;
       signed_true := _;
       signed_false := _ |}.
  - intros A Htrue.
    exact ((proj1 (membership_spec D A)) Htrue).
  - intros A Hfalse.
    apply Hrefutation.
    intro HA.
    pose proof ((proj2 (membership_spec D A)) HA) as Htrue.
    rewrite Hfalse in Htrue.
    discriminate Htrue.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             DIAGONAL PRODUCTION                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The goal frame names only the anti-diagonal behavior
│          required for one fixed goal `G`. It is a supplied
│          representability premise, not an evaluator constructed by
│          L001.
│
*)

Definition ClosureEvaluationFrameForGoal
    (C : Formula -> Prop)
    (Code : Type)
    (ev : Code -> Code -> Formula)
    (G : Formula) : Prop :=
  exists c : Code,
    forall x : Code,
      ClosureEquiv C
        (ev c x)
        (Imp (ev x x) G).
