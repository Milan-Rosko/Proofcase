(*P001_98_02A_Peeling.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / P001_98_02A_Peeling                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This “phase” loads the derived reframing layer and records the remaining
  obligations as named goal packages. The actual discharge of these packages
  is deferred to the next step.

*)

From P001 Require Export P001_01_Reframing.

(*
│
│          Every bounded source element factors into a power of `2`
│          times an odd core.
│
*)

Definition show_two_adic_factorization : Prop :=
  forall n x,
    1 <= x ->
    x <= 2 * n ->
    exists k m,
      x = 2 ^ k * m /\
      Nat.Odd m.

(*
│
│          The odd integers in `1` through `2n` are exhausted by a
│          list of cardinality `n`.
│
*)

Definition show_odd_domain_exhaustion : Prop :=
  forall n,
    exists odd_domain : list nat,
      NoDup odd_domain /\
      length odd_domain = n /\
      forall m,
        In m odd_domain <->
        1 <= m /\ m <= 2 * n /\ Nat.Odd m.

(*
│
│          Any bounded distinct selection of length `n+1` contains two
│          distinct members sharing one odd core.
│
*)

Definition show_odd_core_collision : Prop :=
  forall n A,
    (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->
    NoDup A ->
    length A = n + 1 ->
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

Definition show_common_odd_core_implies_divisibility : Prop :=
  forall n A y z m i j,
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
│          The four remaining goals form one peeling package.
│
*)

Definition peeling_package : Prop :=
  show_two_adic_factorization /\
  show_odd_domain_exhaustion /\
  show_odd_core_collision /\
  show_common_odd_core_implies_divisibility.
