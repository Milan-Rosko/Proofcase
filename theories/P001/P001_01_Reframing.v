(*P001_01_Reframing.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / P001_01_Reframing                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file is the derived semantic layer that sits directly above the
  immutable premises.

  It packages the proof target into smaller semantic components and proves
  that this reframed package implies the original witness.

  ANALOGY

  The reframing layer splits the expanded semantics with higher resolution:

  Level 1: (( We prove ) (( X )( from )( necessity. ))) -> QED

  Level 2: (( We prove ) that (( among any collection of n+1 pairwise
  distinct integers chosen from the integers 1 through 2n, there must exist
  at least two distinct members of that collection such that one of them
  divides the other ( with no remainder ))( from )( necessity ))) -> QED

  Level 3: (( We prove ) that (((( every integer $x$ )( chosen from the
  domain )( 1 through 2n ))( can be strictly factored into )((( the integer 2
  )( raised to the power of )( some non-negative integer $k$ ))( multiplied
  by )( some odd integer $m$ ))) AND (( bounding )(( the maximum count of )(
  distinct odd integers $m$ )( existing between )( 1 and 2n ))( is exactly
  equal to )( $n$ )))( must collide )(( since ) ((( selecting )( a count of
  $n+1$ integers ))( forces )(( at least two selected integers )( $A$ and $B$
  ))( to share )(( the exact same )( odd integer $m$ ))))( which ultimately
  guarantees that )(( by )( $A = 2^j \cdot m$ ) AND ( $B = 2^k \cdot m$ ))((
  the integer possessing )( the smaller power of 2 ))( must perfectly divide
  )(( the integer possessing )( the larger power of 2 ))( with no remainder
  )))) -> QED

  Level 4: Lambda term processed by Rocq.

*)

From P001 Require Export P001_00_Premises.

Definition bounded_selection_package (n : nat)(A : list nat) : Prop :=
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

Definition odd_core_collision_package (n : nat)(A : list nat) : Prop :=
  exists y z m i j,
    In y A /\
    In z A /\
    y <> z /\
    1 <= m /\
    m <= 2 * n /\
    Nat.Odd m /\
    y = 2 ^ i * m /\
    z = 2 ^ j * m.

Definition odd_core_divisibility_package (n : nat)(A : list nat) : Prop :=
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
│          The reframed package is still a “stronger” claim than the
│          original witness because the divisibility package applies
│          to the collision package.
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
