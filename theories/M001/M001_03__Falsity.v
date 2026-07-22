(*M001_03__Falsity.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / M001_03__Falsity                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Executable constructive reductio. Object-language negation is defined with
  the primitive syntax in `M001_00`; this layer specializes the checked
  deduction transformer to conclusion `Bot`. A checked contradiction under a
  temporary assumption `A` is thereby transformed into a checked proof of `A
  -> Bot` after the assumption is discharged.

  The transform and its checker theorem are the complete public surface.
  Reductio certificates require no separate hierarchy: callers may retain the
  source script, compute the target script, and validate either one with the
  ordinary checker.

*)

From M001 Require Export M001_02__Abstraction.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               CHECKED REDUCTIO                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition regulator_theory_reductio_transform
    (A : Formula)
    (p : Proof) : Proof :=
  regulator_theory_deduction_transform A p.

(*
│
│          The reductio theorem is constructive and
│          profile-independent. It is exactly checked deduction at the
│          conclusion `Bot`.
│
*)

Theorem regulator_theory_reductio_checked :
  forall R Gamma A p,
    regulator_theory_check_bool R (ctx_extend A Gamma) p Bot = true ->
    regulator_theory_check_bool
      R
      Gamma
      (regulator_theory_reductio_transform A p)
      (formula_negation A) = true.
Proof.
  intros R Gamma A p Hcheck.
  unfold regulator_theory_reductio_transform,
    formula_negation.
  exact (regulator_theory_deduction_checked R Gamma A Bot p Hcheck).
Qed.
