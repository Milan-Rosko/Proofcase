(*S002_91_02B__Rewrite.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / S002_91_02B__Rewrite                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This conjectural rewrite presentation rebuilds the reframed package from
  four named obligations and then derives `WITNESS`. It records a historical
  proof layer; the terminal switch selects the completed proof in
  `S002_91_02C__Proof`.

*)

From S002 Require Export S002_01__Reframing.

(*
│
│          The rewrite assembly packages four named obligations
│          matching the semantic components exported by the reframing
│          layer.
│
*)

Module Export four_conjectures.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          REWRITE OBLIGATION PACKAGE                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
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
│          Any bounded distinct selection of length `n + 1` contains
│          two distinct members sharing one odd core.
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
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               REWRITE ASSEMBLY                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The four named obligations assemble into the reframed
│          expansion.
│
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

(*
│
│          The assembled reframing package gives `WITNESS`.
│
*)

Theorem UNCONDITIONAL_PROOF : WITNESS.
Proof.
  apply first_expansion_implies_WITNESS.
  exact the_four_conjectures_hold.
Qed.
