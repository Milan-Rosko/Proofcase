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

  Checked certificate vocabulary for regulator theories. The previous layers
  provide primitive syntax (`M001_00`), a Boolean checker over
  `RegulatorTheory` (`M001_01`), checked deduction (`M001_02`), and checked
  constructive reductio (`M001_03`). This file packages those checked scripts
  into reusable proof-certificate and checked-derivability predicates while
  preserving the object logic.

  The central distinction is between a retained and a forgotten certificate.
  `regulator_theory_proof_certificate R Γ A` stores a concrete finite script
  together with its checker equation. `regulator_theory_checked_derivable R Γ
  A` forgets the script into a Prop-level existential. The finite-axiom-set
  and minimal-profile variants wrap the same Boolean checker interfaces
  introduced in `M001_01`.

*)

From M001 Require Export M001_03__Falsity.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          CHECKED PROOF CERTIFICATES                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `regulator_theory_proof_certificate R Γ A` pairs a finite
│          proof script with its acceptance by
│          `regulator_theory_check_bool` as a proof of `A` from `Γ`
│          under `R`. The certificate remains extractable and
│          inspectable at the syntactic checker level.
│
*)

(*RegProof(R, Γ, A) ≔ { p : Proof ∣ regulator_theory_check_bool(R, Γ, p, A) = *)
(*                                   true }                                   *)

Definition regulator_theory_proof_certificate
    (R : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Type :=
  { p : Proof | regulator_theory_check_bool R Gamma p A = true }.

Definition regulator_theory_proof_certificate_script
    {R : RegulatorTheory}
    {Gamma : Context}
    {A : Formula}
    (c : regulator_theory_proof_certificate R Gamma A) : Proof :=
  proj1_sig c.

Lemma regulator_theory_proof_certificate_checked_lemma :
  forall R Gamma A
    (c : regulator_theory_proof_certificate R Gamma A),
    regulator_theory_check_bool
      R
      Gamma
      (regulator_theory_proof_certificate_script c)
      A = true.
Proof.
  intros R Gamma A c.
  destruct c as [p Hp].
  exact Hp.
Qed.

Definition regulator_theory_proof_certificate_from_checked
    (R : RegulatorTheory)
    (Gamma : Context)
    (A : Formula)
    (p : Proof)
    (H : regulator_theory_check_bool R Gamma p A = true)
    : regulator_theory_proof_certificate R Gamma A :=
  exist _ p H.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             CHECKED DERIVABILITY                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `regulator_theory_checked_derivable` forgets the proof
│          script into the existential claim that the Boolean checker
│          accepts some finite script. Its negative form negates that
│          same syntactic existence claim.
│
*)

(*                    R; Γ ⊢check A ≔ ∃p, R; Γ ⊢check[p] A                    *)
(*                  R; Γ ⊬check A ≔ (R; Γ ⊢check A) → False                   *)

Definition regulator_theory_checked_derivable
    (R : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Prop :=
  exists p : Proof,
    regulator_theory_check_bool R Gamma p A = true.

Definition regulator_theory_not_checked_derivable
    (R : RegulatorTheory)
    (Gamma : Context)
    (A : Formula) : Prop :=
  regulator_theory_checked_derivable R Gamma A -> False.

(*
│
│          The minimal and finite-axiom-set variants are
│          checker-facing conveniences. The minimal variant fixes the
│          profile through `regulator_theory_check_minimal_bool`; the
│          finite variant keeps the finite axiom list visible and
│          checks through `finite_axiom_set_check_bool`.
│
*)

(*                T; Γ ⊢check_min A ≔ ∃p, T; Γ ⊢check_min[p] A                *)
(*                       profile, FT; Γ ⊢check A ≔ ∃p,                        *)
(*             finite_axiom_set_check_bool(profile,FT,Γ,p,A)=true             *)

Definition regulator_theory_minimal_checked_derivable
    (T : AxiomSet)
    (Gamma : Context)
    (A : Formula) : Prop :=
  exists p : Proof,
    regulator_theory_check_minimal_bool T Gamma p A = true.

Definition finite_axiom_set_checked_derivable
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    (A : Formula) : Prop :=
  exists p : Proof,
    finite_axiom_set_check_bool profile T Gamma p A = true.

Definition finite_axiom_set_not_checked_derivable
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    (A : Formula) : Prop :=
  finite_axiom_set_checked_derivable profile T Gamma A -> False.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             CERTIFICATE BRIDGES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                      RegProof(R,Γ,A) ⇒ R; Γ ⊢check A                       *)

Lemma regulator_theory_proof_certificate_derivable_lemma :
  forall R Gamma A,
    regulator_theory_proof_certificate R Gamma A ->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A c.
  exists (regulator_theory_proof_certificate_script c).
  apply regulator_theory_proof_certificate_checked_lemma.
Qed.

Lemma regulator_theory_check_bool_derivable_lemma :
  forall R Gamma A p,
    regulator_theory_check_bool R Gamma p A = true ->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A p Hp.
  exists p.
  exact Hp.
Qed.

(*                            T; Γ ⊢check_min A ⇔                             *)
(*  regulator_theory_with_axiom_set(regulator_profile_minimal,T); Γ ⊢check A  *)

Lemma regulator_theory_minimal_checked_derivable_as_theory_lemma :
  forall T Gamma A,
    regulator_theory_minimal_checked_derivable T Gamma A <->
    regulator_theory_checked_derivable
      (regulator_theory_with_axiom_set regulator_profile_minimal T)
      Gamma A.
Proof.
  intros T Gamma A.
  split; intros Hder;
    destruct Hder as [p Hp];
    exists p;
    unfold regulator_theory_check_minimal_bool in *;
    exact Hp.
Qed.

(*profile, FT; Γ ⊢check A ⇔ finite_axiom_set_to_regulator_theory(profile,FT); *)
(*                                 Γ ⊢check A                                 *)

Lemma finite_axiom_set_checked_derivable_as_regulator_theory_lemma :
  forall profile T Gamma A,
    finite_axiom_set_checked_derivable profile T Gamma A <->
    regulator_theory_checked_derivable
      (finite_axiom_set_to_regulator_theory profile T)
      Gamma A.
Proof.
  intros profile T Gamma A.
  split; intros Hder;
    destruct Hder as [p Hp];
    exists p;
    unfold finite_axiom_set_check_bool in *;
    exact Hp.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         DEDUCTION AND REDUCTIO LIFTS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The deduction lift is the existential form of
│          `regulator_theory_deduction_checked`: destruct a checked
│          derivability witness under `A :: Γ`, run the deduction
│          transform on its script, and use the checked deduction
│          theorem to check the transformed script under `Γ`.
│
*)

(*                    R; A::Γ ⊢check B ⇒ R; Γ ⊢check A → B                    *)

Lemma regulator_theory_checked_derivable_deduction_lemma :
  forall R Gamma A B,
    regulator_theory_checked_derivable R (ctx_extend A Gamma) B ->
    regulator_theory_checked_derivable R Gamma (Imp A B).
Proof.
  intros R Gamma A B Hder.
  destruct Hder as [p Hp].
  exists (regulator_theory_deduction_transform A p).
  apply regulator_theory_deduction_checked.
  exact Hp.
Qed.

Lemma regulator_theory_minimal_checked_derivable_deduction_lemma :
  forall T Gamma A B,
    regulator_theory_minimal_checked_derivable T (ctx_extend A Gamma) B ->
    regulator_theory_minimal_checked_derivable T Gamma (Imp A B).
Proof.
  intros T Gamma A B Hder.
  destruct Hder as [p Hp].
  exists (regulator_theory_deduction_transform A p).
  apply regulator_theory_deduction_minimal_checked.
  exact Hp.
Qed.

(*
│
│          The reductio lift is the existential form of
│          `regulator_theory_reductio_checked`: a checked derivability
│          witness for `Bot` under `A :: Γ` yields a checked
│          derivability witness for `formula_negation A` under `Γ`.
│
*)

(*                     R; A::Γ ⊢check ⊥ ⇒ R; Γ ⊢check ¬A                      *)

Lemma regulator_theory_checked_derivable_reductio_lemma :
  forall R Gamma A,
    regulator_theory_checked_derivable R (ctx_extend A Gamma) Bot ->
    regulator_theory_checked_derivable R Gamma (formula_negation A).
Proof.
  intros R Gamma A Hder.
  destruct Hder as [p Hp].
  exists (regulator_theory_reductio_transform A p).
  apply regulator_theory_reductio_checked.
  exact Hp.
Qed.

Lemma regulator_theory_minimal_checked_derivable_reductio_lemma :
  forall T Gamma A,
    regulator_theory_minimal_checked_derivable T (ctx_extend A Gamma) Bot ->
    regulator_theory_minimal_checked_derivable T Gamma (formula_negation A).
Proof.
  intros T Gamma A Hder.
  destruct Hder as [p Hp].
  exists (regulator_theory_reductio_transform A p).
  apply regulator_theory_reductio_minimal_checked.
  exact Hp.
Qed.
