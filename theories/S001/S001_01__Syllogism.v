(*S001_01__Syllogism.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / S001_01__Syllogism                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We start off with propositional logic, sometimes called zeroth-order logic.
  It deals with propositions (which can be true or false) and relations
  between propositions.

*)

From S001 Require Export S001_00_Premises.

Section Propositional_Basics.

Variables P Q R : Prop.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   Identity                                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A proof of `P -> P` simply returns the original assumption.
│
*)

Theorem identity :
  P -> P.
Proof.
  intro HP.
  exact HP.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         Implication Elimination (MP)                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          If we know `P` and also know `P -> Q`, then we may conclude
│          `Q`.
│
*)

Theorem modus_ponens :
  P ->
  (P -> Q) ->
  Q.
Proof.
  intro HP.
  intro HPQ.
  apply HPQ.
  exact HP.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          Implication Introduction.                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          To prove an implication, we assume its premise.
│
*)

Theorem implication_intro :
  (P -> Q) ->
  P ->
  Q.
Proof.
  intro HPQ.
  intro HP.
  apply HPQ.
  exact HP.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                Polysyllogism                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          If `P` implies `Q`, and `Q` implies `R`, then `P` implies
│          `R`.
│
*)

Theorem hypothetical_syllogism :
  (P -> Q) ->
  (Q -> R) ->
  (P -> R).
Proof.
  intro HPQ.
  intro HQR.
  intro HP.
  apply HQR.
  apply HPQ.
  exact HP.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           Conjunction Introduction                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          To prove `P /\ Q`, we must prove both sides.
│
*)

Theorem and_intro :
  P ->
  Q ->
  P /\ Q.
Proof.
  intro HP.
  intro HQ.
  split.
  - exact HP.
  - exact HQ.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           Conjunction Elimination                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          From `P /\ Q`, we may recover `P`.
│
*)

Theorem and_left :
  P /\ Q ->
  P.
Proof.
  intro HPQ.
  destruct HPQ as [HP HQ].
  exact HP.
Qed.

(*
│
│          From `P /\ Q`, we may recover `Q`.
│
*)

Theorem and_right :
  P /\ Q ->
  Q.
Proof.
  intro HPQ.
  destruct HPQ as [HP HQ].
  exact HQ.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           Disjunction Introduction                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          If `P` is true, then `P \/ Q` is true.
│
*)

Theorem or_intro_left :
  P ->
  P \/ Q.
Proof.
  intro HP.
  left.
  exact HP.
Qed.

(*
│
│          If `Q` is true, then `P \/ Q` is true.
│
*)

Theorem or_intro_right :
  Q ->
  P \/ Q.
Proof.
  intro HQ.
  right.
  exact HQ.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           Disjunction Elimination                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          To use a disjunction, we prove the same conclusion from
│          each possible branch.
│
*)

Theorem or_elim :
  (P \/ Q) ->
  (P -> R) ->
  (Q -> R) ->
  R.
Proof.
  intro HPQ.
  intro HPR.
  intro HQR.

  destruct HPQ as [HP | HQ].

  - apply HPR.
    exact HP.

  - apply HQR.
    exact HQ.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   Negation                                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Negation is defined as implication into contradiction.
│
*)

Check not.

(*
│
│          If assuming `P` leads to contradiction, then we may
│          conclude `~P`.
│
*)

Theorem negation_intro :
  (P -> False) ->
  ~P.
Proof.
  intro HPFalse.
  exact HPFalse.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                Contradiction                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          From contradiction, anything follows.
│
*)

Theorem explosion :
  False ->
  P.
Proof.
  intro HFalse.
  destruct HFalse.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               Double Negation                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Every proposition implies its double negation.
│
*)

Theorem double_negation :
  P ->
  ~~P.
Proof.
  intro HP.
  unfold not.
  intro HNotP.
  apply HNotP.
  exact HP.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                Contrapositive                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          If `P -> Q`, then `~Q -> ~P`.
│
*)

Theorem contrapositive :
  (P -> Q) ->
  (~Q -> ~P).
Proof.
  intro HPQ.
  intro HNotQ.
  intro HP.

  apply HNotQ.
  apply HPQ.
  exact HP.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                Biconditional                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A biconditional is represented as two implications.
│
*)

Theorem iff_intro :
  (P -> Q) ->
  (Q -> P) ->
  P <-> Q.
Proof.
  intro HPQ.
  intro HQP.
  split.
  - exact HPQ.
  - exact HQP.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                Commutativity                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Conjunction is commutative.
│
*)

Theorem and_comm :
  P /\ Q ->
  Q /\ P.
Proof.
  intro HPQ.
  destruct HPQ as [HP HQ].

  split.
  - exact HQ.
  - exact HP.
Qed.

(*
│
│          Disjunction is also commutative.
│
*)

Theorem or_comm :
  P \/ Q ->
  Q \/ P.
Proof.
  intro HPQ.

  destruct HPQ as [HP | HQ].

  - right.
    exact HP.

  - left.
    exact HQ.
Qed.

End Propositional_Basics.
