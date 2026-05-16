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

  Falsity and constructive reductio for regulator theories.
  `M001_00_Premises` supplies `Bot` as the primitive falsity formula,
  `M001_01__Kernel` supplies checked proof scripts over a `RegulatorTheory`,
  and `M001_02__Abstraction` supplies checked deduction. This file names
  object-language negation as implication to falsity and specialises checked
  deduction at conclusion `Bot`: a checked contradiction under `A :: Γ`
  becomes a checked proof of `A → ⊥` under `Γ`.

  The public theorem surface is deliberately small.
  `regulator_theory_constructive_reductio_checked` is the direct
  `Bot`-conclusion theorem; `regulator_theory_reductio_checked` restates the
  conclusion through `formula_negation`; and
  `regulator_theory_reductio_minimal_checked` is the EFQ-free minimal-profile
  form. The certificate records below separate computed reductio
  certificates, whose target proof is the output of the reductio transformer,
  from paired certificates, whose source and target proof scripts are checked
  independently. This file does not introduce semantic validity, external
  model theory, modal provability, arithmetic coding, diagonal obstruction,
  or self-recognition.

*)

From M001 Require Export M001_02__Abstraction.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           OBJECT-LANGUAGE NEGATION                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          We use `formula_negation A` as notation inside the object
│          language: it is exactly the implication from `A` to the
│          primitive falsity formula `Bot`. Thus `formula_negation A`
│          and `Imp A Bot` are definitionally the same formula. This
│          introduces no Rocq-level negation principle and no semantic
│          reading of falsity; it only names the syntactic shape used
│          by the reductio transformer.
│
*)

(*                                 ¬A ≔ A → ⊥                                 *)

Definition formula_negation (A : Formula) : Formula :=
  Imp A Bot.

Lemma formula_negation_unfold_lemma :
  forall A,
    formula_negation A = Imp A Bot.
Proof.
  reflexivity.
Qed.

Lemma formula_negation_congruent_lemma :
  forall A B,
    A = B ->
    formula_negation A = formula_negation B.
Proof.
  intros A B H.
  subst.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        CHECKED CONSTRUCTIVE REDUCTIO                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `regulator_theory_reductio_transform` is the
│          checked-deduction transform viewed at conclusion `Bot`. The
│          function is definitionally the `M001_02` deduction
│          transformer; the separate name records the logical register
│          of the call site: turning a checked contradiction under a
│          temporary hypothesis into a checked proof of that
│          hypothesis's object-language negation.
│
*)

(*     reductio_transform(A,p) ≔ regulator_theory_reductio_transform(A,p)     *)
(*    regulator_theory_reductio_transform(A,p) = deduction_transform(A,p)     *)

Definition regulator_theory_reductio_transform
    (A : Formula)
    (p : Proof) : Proof :=
  regulator_theory_deduction_transform A p.

(*
│
│          `regulator_theory_constructive_reductio_checked` is the
│          direct specialisation of checked deduction at conclusion
│          `Bot`. `regulator_theory_reductio_checked` then rewrites
│          the target formula through `formula_negation`, and
│          `regulator_theory_reductio_minimal_checked` packages the
│          same result for the minimal profile wrapper.
│
*)

(*      R; A::Γ ⊢check[p] ⊥ ⇒ R; Γ ⊢check[reductio_transform(A,p)] A → ⊥      *)

Theorem regulator_theory_constructive_reductio_checked :
  forall R Gamma A p,
    regulator_theory_check_bool R (ctx_extend A Gamma) p Bot = true ->
    regulator_theory_check_bool
      R
      Gamma
      (regulator_theory_reductio_transform A p)
      (Imp A Bot) = true.
Proof.
  intros R Gamma A p Hcheck.
  unfold regulator_theory_reductio_transform.
  exact (regulator_theory_deduction_checked R Gamma A Bot p Hcheck).
Qed.

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
  unfold formula_negation.
  exact (regulator_theory_constructive_reductio_checked R Gamma A p Hcheck).
Qed.

(*   T; A::Γ ⊢check_min[p] ⊥ ⇒ T; Γ ⊢check_min[reductio_transform(A,p)] ¬A    *)

Theorem regulator_theory_reductio_minimal_checked :
  forall T Gamma A p,
    regulator_theory_check_minimal_bool T (ctx_extend A Gamma) p Bot = true ->
    regulator_theory_check_minimal_bool
      T
      Gamma
      (regulator_theory_reductio_transform A p)
      (formula_negation A) = true.
Proof.
  intros T Gamma A p Hcheck.
  unfold regulator_theory_check_minimal_bool in *.
  exact (regulator_theory_reductio_checked
    (regulator_theory_with_axiom_set regulator_profile_minimal T)
    Gamma A p Hcheck).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         REDUCTIO CERTIFICATE SHAPES                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `ComputedReductioCertificate` stores only the source
│          contradiction proof; the target proof of `A → ⊥` is
│          materialised by running
│          `regulator_theory_reductio_transform`. A
│          `PairedReductioCertificate` stores both source and target
│          scripts independently; the paired verifier accepts when
│          both scripts check, without requiring the target to be
│          syntactically equal to the transformer's output.
│
*)

(*          ComputedReductio(A,p) ↦ (A, p, reductio_transform(A,p))           *)
(*                   PairedReductio(A,p₀,p₁) ↦ (A, p₀, p₁)                    *)

Record ComputedReductioCertificate : Type := {
  computed_reductio_assumption : Formula;
  computed_reductio_contradiction_proof : Proof
}.

Definition computed_reductio_certificate_proof
    (c : ComputedReductioCertificate) : Proof :=
  regulator_theory_reductio_transform
    c.(computed_reductio_assumption)
    c.(computed_reductio_contradiction_proof).

Definition make_computed_reductio_certificate
    (A : Formula)
    (p : Proof) : ComputedReductioCertificate :=
  {|
    computed_reductio_assumption := A;
    computed_reductio_contradiction_proof := p
  |}.

Record PairedReductioCertificate : Type := {
  paired_reductio_assumption : Formula;
  paired_reductio_contradiction_proof : Proof;
  paired_reductio_proof : Proof
}.

Definition computed_to_paired_reductio_certificate
    (c : ComputedReductioCertificate) : PairedReductioCertificate :=
  {|
    paired_reductio_assumption := c.(computed_reductio_assumption);
    paired_reductio_contradiction_proof :=
      c.(computed_reductio_contradiction_proof);
    paired_reductio_proof := computed_reductio_certificate_proof c
  |}.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         BOOLEAN CERTIFICATE CHECKERS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `computed_reductio_certificate_check_bool` checks the
│          source contradiction proof and then checks the target proof
│          obtained by actually running the reductio transform. The
│          second check is guaranteed by
│          `regulator_theory_reductio_checked`, but keeping it in the
│          Boolean checker makes the executable artifact boundary
│          explicit.
│
*)

(*    computed_reductio_certificate_check_bool(R,Γ,(A,p)) = true ⇔ R; A::Γ    *)
(*           ⊢check[p] ⊥ ∧ R; Γ ⊢check[reductio_transform(A,p)] ¬A            *)

Definition computed_reductio_certificate_check_bool
    (R : RegulatorTheory)
    (Gamma : Context)
    (c : ComputedReductioCertificate) : bool :=
  let A := c.(computed_reductio_assumption) in
  let p := c.(computed_reductio_contradiction_proof) in
  regulator_theory_check_bool R (ctx_extend A Gamma) p Bot
  &&
  regulator_theory_check_bool
    R
    Gamma
    (computed_reductio_certificate_proof c)
    (formula_negation A).

(*
│
│          `paired_reductio_certificate_check_bool` accepts a paired
│          certificate iff both supplied scripts check independently:
│          the source as a contradiction proof under `A :: Γ`, and the
│          target as a proof of `A → ⊥` under `Γ`. There is no
│          syntactic equality check against the computed transform
│          output; use the computed certificate checker when that
│          stronger relation is required.
│
*)

(*   paired_reductio_certificate_check_bool(R,Γ,(A,p₀,p₁)) = true ⇔ R; A::Γ   *)
(*                     ⊢check[p₀] ⊥ ∧ R; Γ ⊢check[p₁] ¬A                      *)

Definition paired_reductio_certificate_check_bool
    (R : RegulatorTheory)
    (Gamma : Context)
    (c : PairedReductioCertificate) : bool :=
  let A := c.(paired_reductio_assumption) in
  regulator_theory_check_bool
    R
    (ctx_extend A Gamma)
    c.(paired_reductio_contradiction_proof)
    Bot
  &&
  regulator_theory_check_bool
    R
    Gamma
    c.(paired_reductio_proof)
    (formula_negation A).

Theorem make_computed_reductio_certificate_checked :
  forall R Gamma A p,
    regulator_theory_check_bool R (ctx_extend A Gamma) p Bot = true ->
    computed_reductio_certificate_check_bool
      R
      Gamma
      (make_computed_reductio_certificate A p) = true.
Proof.
  intros R Gamma A p Hcheck.
  unfold computed_reductio_certificate_check_bool,
    make_computed_reductio_certificate,
    computed_reductio_certificate_proof.
  simpl.
  rewrite Hcheck.
  simpl.
  exact (regulator_theory_reductio_checked R Gamma A p Hcheck).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        ROCQ-SIDE CHECKED CERTIFICATES                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `CheckedReductioCertificate` is the Rocq-side paired
│          certificate with proof fields. It stores a
│          `RegulatorTheory`, a context, the discharged assumption,
│          both proof scripts, and the two checker equations. It is
│          useful for internal Rocq reasoning about already-checked
│          certificates. The finite external format below is the
│          extraction-facing certificate shape.
│
*)

(*CheckedReductio(R,Γ,A,p₀,p₁) ≔ (R; A::Γ ⊢check[p₀] ⊥) ∧ (R; Γ ⊢check[p₁] ¬A)*)

Record CheckedReductioCertificate : Type := {
  checked_reductio_theory : RegulatorTheory;
  checked_reductio_context : Context;
  checked_reductio_assumption : Formula;
  checked_reductio_contradiction_proof : Proof;
  checked_reductio_proof : Proof;

  checked_reductio_contradiction_checked :
    regulator_theory_check_bool
      checked_reductio_theory
      (ctx_extend checked_reductio_assumption checked_reductio_context)
      checked_reductio_contradiction_proof
      Bot = true;

  checked_reductio_proof_checked :
    regulator_theory_check_bool
      checked_reductio_theory
      checked_reductio_context
      checked_reductio_proof
      (formula_negation checked_reductio_assumption) = true
}.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           RAW FINITE CERTIFICATES                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `RawReductioCertificate` is the finite-data certificate
│          shape. Its axiom source is a `FiniteAxiomSet`, not an
│          arbitrary function-valued `AxiomSet`, so the whole record
│          can be serialised, transmitted, and re-checked by the
│          Boolean verifier. It is paired rather than computed: the
│          verifier checks both scripts independently and does not
│          assert syntactic equality with
│          `regulator_theory_reductio_transform A p`.
│
*)

(*  raw_R(c) ≔ finite_axiom_set_to_regulator_theory(raw_reductio_profile(c),  *)
(*                         raw_reductio_axiom_set(c))                         *)

Record RawReductioCertificate : Type := {
  raw_reductio_profile : RegulatorLogicProfile;
  raw_reductio_axiom_set : FiniteAxiomSet;
  raw_reductio_context : Context;
  raw_reductio_assumption : Formula;
  raw_reductio_contradiction_proof : Proof;
  raw_reductio_proof : Proof
}.

Definition raw_reductio_regulator_theory
    (c : RawReductioCertificate) : RegulatorTheory :=
  finite_axiom_set_to_regulator_theory
    c.(raw_reductio_profile)
    c.(raw_reductio_axiom_set).

Definition raw_to_paired_reductio_certificate
    (c : RawReductioCertificate) : PairedReductioCertificate :=
  {|
    paired_reductio_assumption := c.(raw_reductio_assumption);
    paired_reductio_contradiction_proof :=
      c.(raw_reductio_contradiction_proof);
    paired_reductio_proof := c.(raw_reductio_proof)
  |}.

Definition raw_reductio_certificate_check_bool
    (c : RawReductioCertificate) : bool :=
  paired_reductio_certificate_check_bool
    (raw_reductio_regulator_theory c)
    c.(raw_reductio_context)
    (raw_to_paired_reductio_certificate c).

(*                  raw_reductio_certificate_check_bool(c) =                  *)
(* paired_reductio_certificate_check_bool(raw_R(c), raw_reductio_context(c),  *)
(*                   raw_to_paired_reductio_certificate(c))                   *)

Definition make_raw_reductio_certificate
    (profile : RegulatorLogicProfile)
    (FT : FiniteAxiomSet)
    (Gamma : Context)
    (A : Formula)
    (p : Proof) : RawReductioCertificate :=
  {|
    raw_reductio_profile := profile;
    raw_reductio_axiom_set := FT;
    raw_reductio_context := Gamma;
    raw_reductio_assumption := A;
    raw_reductio_contradiction_proof := p;
    raw_reductio_proof := regulator_theory_reductio_transform A p
  |}.

Theorem make_raw_reductio_certificate_checked :
  forall profile FT Gamma A p,
    finite_axiom_set_check_bool profile FT (ctx_extend A Gamma) p Bot = true ->
    raw_reductio_certificate_check_bool
      (make_raw_reductio_certificate profile FT Gamma A p) = true.
Proof.
  intros profile FT Gamma A p Hcheck.
  unfold raw_reductio_certificate_check_bool,
    raw_to_paired_reductio_certificate,
    paired_reductio_certificate_check_bool,
    raw_reductio_regulator_theory,
    make_raw_reductio_certificate.
  simpl.
  unfold finite_axiom_set_check_bool in Hcheck.
  rewrite Hcheck.
  simpl.
  exact (regulator_theory_reductio_checked
    (finite_axiom_set_to_regulator_theory profile FT)
    Gamma A p Hcheck).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           CERTIFICATE DIAGNOSTICS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The diagnostic helpers below report finite certificate
│          shape only: proof lengths and the advertised reductio
│          conclusion. They are not part of the trusted checking path
│          and downstream proof layers should not depend on them as
│          stable logical interfaces.
│
*)

Definition proof_script_length (p : Proof) : nat :=
  length p.

Definition raw_reductio_certificate_reductio_length
    (c : RawReductioCertificate) : nat :=
  proof_script_length c.(raw_reductio_proof).

Definition raw_reductio_certificate_contradiction_length
    (c : RawReductioCertificate) : nat :=
  proof_script_length c.(raw_reductio_contradiction_proof).

Definition raw_reductio_certificate_conclusion
    (c : RawReductioCertificate) : Formula :=
  formula_negation c.(raw_reductio_assumption).
