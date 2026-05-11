(*S002_01__Reframing.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / S002_01__Reframing                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file packages the divisibility theorem into semantic components and
  proves that the package implies `WITNESS`.

  STRUCTURE

  The components state bounded selection, factorization into a power of two
  times an odd core, the finite odd-domain count, the forced collision of odd
  cores, and the divisibility orientation obtained from such a collision.

*)

From S002 Require Export S002_00_Premises.

(*
│
│          A bounded selection is a duplicate-free list of exactly `n
│          + 1` integers drawn from `1` through `2n`.
│
*)

Definition bounded_selection_package (n : nat) (A : list nat) : Prop :=
  (forall a, In a A -> 1 <= a /\ a <= 2 * n) /\
  NoDup A /\
  length A = n + 1.

(*
│
│          Every positive integer in the bounded interval decomposes
│          as a power of `2` times an odd integer.
│
*)

Definition two_adic_factorization_package (n : nat) : Prop :=
  forall x,
    1 <= x ->
    x <= 2 * n ->
    exists k m,
      x = 2 ^ k * m /\
      Nat.Odd m.

(*
│
│          The odd integers in `1` through `2n` form a duplicate-free
│          domain of size `n`.
│
*)

Definition odd_domain_package (n : nat) : Prop :=
  exists odd_domain : list nat,
    NoDup odd_domain /\
    length odd_domain = n /\
    forall m,
      In m odd_domain <->
      1 <= m /\ m <= 2 * n /\ Nat.Odd m.

(*
│
│          Among `n + 1` bounded distinct integers, two share the same
│          odd core.
│
*)

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

(*
│
│          Two distinct selected integers with the same odd core are
│          ordered by divisibility.
│
*)

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
│          The reframed expansion above says that any bounded distinct
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
│          The reframed package implies the original witness because
│          the divisibility package applies to the colliding pair.
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
