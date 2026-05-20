(*S002_02__Quantifiers.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / S002_02__Quantifiers                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We extend the propositional formulary from implication and connectives to
  universal and existential reasoning: predicates depending on values, proof
  terms carrying witnesses, specialization of universal assumptions,
  destruction of existential assumptions, and a first equality bridge toward
  rewriting.

*)

From S002 Require Export S002_01__Syllogisms.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           UNIVERSAL QUANTIFICATION                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A universally quantified theorem may be read as a function
│          that accepts a proposition and then a proof of that
│          proposition. The proof returns the assumption it was given.
│
*)

Theorem forall_identity :
  forall P : Prop,
    P -> P.
Proof.
  intro P.
  intro HP.
  exact HP.
Qed.

(*
│
│          Universal quantification also ranges over data. If `P` is a
│          predicate on values of type `A`, then a proof of `forall x,
│          P x` can be applied to any particular value `a`.
│
*)

Theorem forall_predicate_identity :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, P x) ->
    forall a : A, P a.
Proof.
  intros A P Hall a.
  apply Hall.
Qed.

(*
│
│          The same construction can be written as an explicit proof
│          term: the proof depends on the chosen value `a` by applying
│          `Hall` to it.
│
*)

Theorem forall_predicate_identity_term :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, P x) ->
    forall a : A, P a.
Proof.
  exact
    (fun A P Hall a =>
       Hall a).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          EXISTENTIAL QUANTIFICATION                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          To prove an existential proposition, provide a witness and
│          then prove that the witness satisfies the predicate. Here
│          the witness is `0`, and the predicate is equality with
│          itself.
│
*)

Theorem exists_example :
  exists n : nat,
    n = n.
Proof.
  exists 0.
  reflexivity.
Qed.

(*
│
│          A witness may come from the surrounding context. For every
│          natural number `n`, the same `n` witnesses the proposition
│          `exists m, m = n`.
│
*)

Theorem exists_with_context_value :
  forall n : nat,
    exists m : nat,
      m = n.
Proof.
  intro n.
  exists n.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            UNIVERSAL ELIMINATION                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Universal elimination is specialization: a proof of `forall
│          n, n = n` can be used at the particular value `3`.
│
*)

Theorem forall_use :
  (forall n : nat, n = n) ->
  3 = 3.
Proof.
  intro Hall.
  apply Hall.
Qed.

(*
│
│          Specialization works for arbitrary predicates, not only
│          equality. The universal assumption `Hall` is specialized at
│          the concrete value `3`.
│
*)

Theorem forall_specialize :
  forall P : nat -> Prop,
    (forall n : nat, P n) ->
    P 3.
Proof.
  intros P Hall.
  specialize (Hall 3).
  exact Hall.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           EXISTENTIAL ELIMINATION                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          To use an existential assumption, destruct it into a
│          witness and a proof about that witness. Even when the final
│          goal is trivial, the proof object has exposed the data
│          carried by the existential.
│
*)

Theorem exists_use :
  (exists n : nat, n = 0) ->
  True.
Proof.
  intro Hexists.
  destruct Hexists as [n Hn].
  exact I.
Qed.

(*
│
│          Existential elimination becomes useful when a universal
│          rule transforms the predicate attached to the witness. The
│          same witness is repackaged after the rule is applied.
│
*)

Theorem exists_map :
  forall P Q : nat -> Prop,
    (forall n : nat, P n -> Q n) ->
    (exists n : nat, P n) ->
    exists n : nat, Q n.
Proof.
  intros P Q HPQ Hexists.
  destruct Hexists as [n HPn].
  exists n.
  apply HPQ.
  exact HPn.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              PREDICATE EXAMPLES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Section Predicate_Examples.

Variable Even : nat -> Prop.

(*
│
│          A predicate such as `Even : nat -> Prop` assigns a
│          proposition to each natural number. A universal rule over
│          such a predicate may be applied to a concrete input.
│
*)

Theorem predicate_step_use :
  (forall n : nat, Even n -> Even (n + 2)) ->
  Even 4 ->
  Even (4 + 2).
Proof.
  intro Hstep.
  intro H4.
  apply Hstep.
  exact H4.
Qed.

(*
│
│          The same universal rule may be chained: first apply it at
│          `0`, then apply it again at `0 + 2`.
│
*)

Theorem predicate_step_twice :
  (forall n : nat, Even n -> Even (n + 2)) ->
  Even 0 ->
  Even ((0 + 2) + 2).
Proof.
  intro Hstep.
  intro H0.
  apply Hstep.
  apply Hstep.
  exact H0.
Qed.

End Predicate_Examples.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            BASIC EVERYDAY EXAMPLE                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Section Basic_Everyday_Example.

Variables Person Badge : Type.

Variable badge_of : Person -> Badge.
Variable HasBadge : Person -> Prop.
Variable BadgePrinted : Badge -> Prop.

(*
│
│          A universal rule can be used like a workplace policy: if
│          every person with a badge has a printed badge, then a
│          particular employee with a badge has a printed badge.
│
*)

Theorem employee_badge_policy_applies_to_employee :
  forall employee : Person,
    (forall person : Person,
       HasBadge person ->
       BadgePrinted (badge_of person)) ->
    HasBadge employee ->
    BadgePrinted (badge_of employee).
Proof.
  intros employee badge_policy employee_has_badge.
  apply badge_policy.
  exact employee_has_badge.
Qed.

(*
│
│          An existential proof carries a concrete witness. If someone
│          has a badge, then there exists a person with a badge.
│
*)

Theorem employee_with_badge_is_some_badged_person :
  forall employee : Person,
    HasBadge employee ->
    exists person : Person,
      HasBadge person.
Proof.
  intros employee employee_has_badge.
  exists employee.
  exact employee_has_badge.
Qed.

End Basic_Everyday_Example.

(*
│
│          Predicates need not be primitive. Here `SelfEqual n` is the
│          proposition that `n` is equal to itself.
│
*)

Definition SelfEqual (n : nat) : Prop :=
  n = n.

Theorem all_self_equal :
  forall n : nat,
    SelfEqual n.
Proof.
  intro n.
  unfold SelfEqual.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               EQUALITY BRIDGE                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Equality is itself a proposition. Reflexivity proves that
│          every natural number is equal to itself.
│
*)

Theorem equality_refl :
  forall x : nat,
    x = x.
Proof.
  intro x.
  reflexivity.
Qed.

(*
│
│          Symmetry reverses an equality proof. This is the first step
│          toward rewriting: an equality can transport information
│          from one side to the other.
│
*)

Theorem equality_sym :
  forall x y : nat,
    x = y ->
    y = x.
Proof.
  intros x y Hxy.
  symmetry.
  exact Hxy.
Qed.

(*
│
│          A predicate proof can be transported across equality. If `x
│          = y` and `P x` holds, then `P y` holds as well.
│
*)

Theorem equality_transport_predicate :
  forall (P : nat -> Prop) (x y : nat),
    x = y ->
    P x ->
    P y.
Proof.
  intros P x y Hxy HPx.
  rewrite <- Hxy.
  exact HPx.
Qed.
