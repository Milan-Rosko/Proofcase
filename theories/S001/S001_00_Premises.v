(*S001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / S001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  S001 is a general logic formulary. This opening file starts as a tutorial
  layer for elementary propositional reasoning and is meant to grow by small,
  readable additions.

*)

From Stdlib Require Export Init.Logic.

  PROPOSITIONAL BASICS

Section Propositional_Basics.

Variables P Q R : Prop.

(*
│
│          A proof of `P -> P` is just the original assumption.
│
*)

Theorem identity : P -> P.
Proof.
  intro HP.
  exact HP.
Qed.

(*
│
│          To prove a conjunction, prove both sides.
│
*)

Theorem conjunction_intro : P -> Q -> P /\ Q.
Proof.
  intros HP HQ.
  split; assumption.
Qed.

(*
│
│          To use a conjunction, destruct it into its two components.
│
*)

Theorem conjunction_elim_left : P /\ Q -> P.
Proof.
  intro H.
  destruct H as [HP _].
  exact HP.
Qed.

(*
│
│          Implications compose: if `P` implies `Q` and `Q` implies
│          `R`, then `P` implies `R`.
│
*)

Theorem implication_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros HPQ HQR HP.
  apply HQR.
  apply HPQ.
  exact HP.
Qed.

End Propositional_Basics.
