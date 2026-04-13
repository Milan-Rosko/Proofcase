(*P001_98_02B_Rewrite.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / P001_98_02B_Rewrite                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This stage no longer carries the derived or conjectural payload.

  The derived semantic content now lives in `P001_01_Reframing`, while the
  remaining conjectural payload lives in `P001_98_01_0_Peeling`.

*)

From P001 Require Export P001_01_Reframing.

From P001 Require Export P001_00_Premises.

(*
│
│          The reframing layer splits the expanded sentence into
│          smaller semantic packages.
│
*)

Definition bounded_selection_package (n : nat) (A : list nat) : Prop :=
  (forall a, In a A -> 1 <= a /\ a <= 2 * n) /\
  NoDup A /\
  length A = n + 1.

Definition two_adic_factorization_package (n : nat) : Prop :=
  forall x,
    1 <= x ->
    x <= 2 * n ->
    exists k m,
      x = 2 ^ k * m /\
      Nat.Odd m.

Definition odd_domain_package (n : nat) : Prop :=
  exists odd_domain : list nat,
    NoDup odd_domain /\
    length odd_domain = n /\
    forall m,
      In m odd_domain <->
      1 <= m /\ m <= 2 * n /\ Nat.Odd m.

Definition odd_core_collision_package (n : nat) (A : list nat) : Prop :=
  exists y z m i j,
    In y A /\
    In z A /\
    y <> z /\
    1 <= m /\
    m <= 2 * n /\
    Nat.Odd m /\
    y = 2 ^ i * m /\
    z = 2 ^ j * m.

Definition odd_core_divisibility_package (n : nat) (A : list nat) : Prop :=
  forall y z m i j,
    In y A ->
    In z A ->
    y <> z ->
    1 <= m ->
    m <= 2 * n ->
    Nat.Odd m ->
    y = 2 ^ i * m ->
    z = 2 ^ j * m ->
    Nat.divide y z \/ Nat.divide z y.

(*
│
│          The reframed expansion says that any bounded distinct
│          selection of size `n + 1` comes equipped with
│          factorization, odd-domain, collision, and divisibility
│          packages.
│
*)
Definition first_expansion : Prop :=
  forall n A,
    bounded_selection_package n A ->
    two_adic_factorization_package n /\
    odd_domain_package n /\
    odd_core_collision_package n A /\
    odd_core_divisibility_package n A.

(*
│
│          The reframed package is stronger than the original witness
│          because the divisibility package applies to the collision
│          package.
│
*)
Theorem first_expansion_implies_WITNESS :
  first_expansion ->
  WITNESS.
Proof.
  intros Hexp.
  intros n A Hbounds Hnodup Hlen.
  pose proof (conj Hbounds (conj Hnodup Hlen)) as Hselection.
  destruct (Hexp n A Hselection) as [_ [_ [Hcollision Horient]]].
  destruct Hcollision as
      [y [z [m [i [j [Hy [Hz [Hneq [Hm_pos [Hm_bound [Hm_odd [Hy_eq Hz_eq]]]]]]]]]]]].
  exists y, z.
  repeat split; try assumption.
  exact (Horient y z m i j Hy Hz Hneq Hm_pos Hm_bound Hm_odd Hy_eq Hz_eq).
Qed.

(*
│
│          At the rewrite stage, the single endpoint conjecture is
│          split into four smaller conjectures matching the semantic
│          packages above.
│
*)

Module Export four_conjectures.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                        REWRITE CONJECTURE PACKAGE                       ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          Every bounded source element factors into a power of `2`
│          times an odd core.
│
*)
Conjecture show_two_adic_factorization :
  forall n,
    two_adic_factorization_package n.

(*
│
│          The odd integers in `1` through `2n` are exhausted by a
│          list of cardinality `n`.
│
*)
Conjecture show_odd_domain_exhaustion :
  forall n,
    odd_domain_package n.

(*
│
│          Any bounded distinct selection of length `n+1` contains two
│          distinct members sharing one odd core.
│
*)
Conjecture show_odd_core_collision :
  forall n A,
    bounded_selection_package n A ->
    odd_core_collision_package n A.

(*
│
│          Two distinct selected integers with the same odd core are
│          ordered by divisibility.
│
*)
Conjecture show_common_odd_core_implies_divisibility :
  forall n A,
    odd_core_divisibility_package n A.

End four_conjectures.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                             REWRITE ASSEMBLY                            ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

Theorem the_four_conjectures_hold :
  first_expansion.
Proof.
  intros n A Hselection.
  split.
  - exact (show_two_adic_factorization n).
  - split.
    + exact (show_odd_domain_exhaustion n).
    + split.
      * exact (show_odd_core_collision n A Hselection).
      * exact (show_common_odd_core_implies_divisibility n A).
Qed.

Theorem UNCONDITIONAL_PROOF : WITNESS.
Proof.
  apply first_expansion_implies_WITNESS.
  exact the_four_conjectures_hold.
Qed.
