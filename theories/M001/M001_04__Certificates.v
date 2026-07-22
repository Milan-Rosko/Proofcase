(*M001_04__Certificates.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / M001_04__Certificates                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Minimal checked-derivability vocabulary. A proof certificate retains one
  finite script and its checker equation; checked derivability forgets the
  script into an existential proposition. These two views are the only
  certificate surfaces needed by M001 and L002.

*)

From M001 Require Export M001_03__Falsity.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          CHECKED PROOF CERTIFICATES                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition regulator_theory_proof_certificate
    (R : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Type :=
  { p : Proof | regulator_theory_check_bool R Gamma p A = true }.

Definition regulator_theory_checked_derivable
    (R : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Prop :=
  exists p : Proof,
    regulator_theory_check_bool R Gamma p A = true.

(*
│
│          Forgetting a retained certificate preserves its checked
│          derivability claim.
│
*)

Lemma regulator_theory_proof_certificate_derivable_lemma :
  forall R Gamma A,
    regulator_theory_proof_certificate R Gamma A ->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A [p Hp].
  exists p.
  exact Hp.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                DEDUCTION LIFT                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Checked deduction lifts from concrete scripts to
│          existential checked derivability by retaining the
│          transformed script as witness.
│
*)

Lemma regulator_theory_checked_derivable_deduction_lemma :
  forall R Gamma A B,
    regulator_theory_checked_derivable R (ctx_extend A Gamma) B ->
    regulator_theory_checked_derivable R Gamma (Imp A B).
Proof.
  intros R Gamma A B [p Hp].
  exists (regulator_theory_deduction_transform A p).
  exact (regulator_theory_deduction_checked R Gamma A B p Hp).
Qed.
