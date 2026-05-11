(*M001_98_Sanity.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                          Proofcase / M001_98_Sanity                          │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Local sanity probes for the active M001 API. The examples below exercise
  formula equality, context membership, axiom recognition, assumption and MP
  checking, finite axiom sets, deduction, reductio, certificate checking,
  checked and inductive derivability, negative precomposition,
  symbolic-regulator identities, machine aliases, and evaluation closure.
  They are small compile-time witnesses, not a separate theorem layer.

  This file deliberately imports only `M001_95_API`: it checks the public
  operational surface as downstream users would see it. The probes do not
  assert global consistency, semantic validity, model existence, modal
  provability, arithmetic coding, diagonal obstruction, or self-recognition.

*)

From M001 Require Import M001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          BASIC CHECKER COMPUTATION                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The first probes fix the smallest computable facts used by the later
  examples: formula equality is structural, context membership is Boolean
  list membership, and a single assumption line checks when its formula is
  present in the context.

(*                         formula_eq_bool(A,A)=true                          *)
(*                        ctx_mem_bool(A, A :: Γ)=true                        *)
(*                     R; A::Γ ⊢check(pl_assumption A) A                      *)
(*                regulator_theory_check_bool(R,Γ,[],A)=false                 *)

Definition sanity_A : Formula := Bot.

Definition sanity_B : Formula := Imp Bot Bot.

Definition sanity_implication : Formula :=
  Imp sanity_A sanity_B.

Definition sanity_assumption_proof (A : Formula) : Proof :=
  cons (pl_assumption A) nil.

Example sanity_formula_eq_bool_refl :
  formula_eq_bool sanity_A sanity_A = true.
Proof.
  reflexivity.
Qed.

Example sanity_formula_eq_bool_mismatch :
  formula_eq_bool sanity_A sanity_B = false.
Proof.
  reflexivity.
Qed.

Example sanity_context_membership_head :
  forall A Gamma,
    ctx_mem_bool A (ctx_extend A Gamma) = true.
Proof.
  apply ctx_mem_bool_extend_self_lemma.
Qed.

Example sanity_assumption_line_checks :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    (ctx_extend sanity_A ctx_empty)
    (sanity_assumption_proof sanity_A)
    sanity_A = true.
Proof.
  reflexivity.
Qed.

Example sanity_empty_script_rejected :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    ctx_empty
    nil
    sanity_A = false.
Proof.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         AXIOMS AND FINITE AXIOM SETS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  K is available as a logical axiom in the minimal profile. A finite axiom
  set can also contribute a non-logical formula directly; the finite checker
  bridges that finite list into the same regulator-theory checker.

(*                            K(A,B) ≔ A → (B → A)                            *)
(*                     regulator_profile_minimal ⊢ K(A,B)                     *)
(*  regulator_profile_minimal ⊬ ⊥ → A and regulator_profile_with_efq ⊢ ⊥ → A  *)
(*                    A ∈ finite_axiom_set_formulas(FT) ⇒                     *)
(*                 finite_axiom_set_contains_bool(FT,A)=true                  *)
(*            finite_axiom_set_checked_derivable(profile,FT,Γ,A) ⇔            *)
(*regulator_theory_checked_derivable(finite_axiom_set_to_regulator_theory(profile,FT),Γ,A)*)

Definition sanity_K_formula : Formula :=
  Imp sanity_A (Imp sanity_B sanity_A).

Definition sanity_K_proof : Proof :=
  cons (pl_axiom sanity_K_formula) nil.

Example sanity_K_axiom_checks :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    ctx_empty
    sanity_K_proof
    sanity_K_formula = true.
Proof.
  reflexivity.
Qed.

Definition sanity_efq_formula : Formula :=
  Imp Bot Bot.

Definition sanity_efq_proof : Proof :=
  cons (pl_axiom sanity_efq_formula) nil.

Example sanity_efq_rejected_minimal :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    ctx_empty
    sanity_efq_proof
    sanity_efq_formula = false.
Proof.
  reflexivity.
Qed.

Example sanity_efq_accepted_with_efq :
  regulator_theory_check_bool
    regulator_theory_empty_with_efq
    ctx_empty
    sanity_efq_proof
    sanity_efq_formula = true.
Proof.
  reflexivity.
Qed.

Definition sanity_finite_axiom_set : FiniteAxiomSet :=
  {| finite_axiom_set_formulas := cons sanity_A nil |}.

Definition sanity_finite_axiom_proof : Proof :=
  cons (pl_axiom sanity_A) nil.

Example sanity_finite_axiom_set_contains :
  finite_axiom_set_contains_bool
    sanity_finite_axiom_set
    sanity_A = true.
Proof.
  reflexivity.
Qed.

Example sanity_finite_axiom_set_checks :
  finite_axiom_set_check_bool
    regulator_profile_minimal
    sanity_finite_axiom_set
    ctx_empty
    sanity_finite_axiom_proof
    sanity_A = true.
Proof.
  reflexivity.
Qed.

Example sanity_finite_axiom_set_derivable :
  finite_axiom_set_checked_derivable
    regulator_profile_minimal
    sanity_finite_axiom_set
    ctx_empty
    sanity_A.
Proof.
  apply finite_axiom_set_checked_derivable_axiom_lemma.
  left.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         MODUS PONENS AND TRANSFORMS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The MP checker accepts both reference orientations. We also probe the
  certified deduction and reductio transforms by applying their public
  checker theorems to concrete proof scripts.

(*       prefix[0]=A ∧ prefix[1]=A→B ⇒ mp_valid_bool(prefix,0,1,B)=true       *)
(*       prefix[0]=A ∧ prefix[1]=A→B ⇒ mp_valid_bool(prefix,1,0,B)=true       *)
(*              R; Γ ⊢check A→B ∧ R; Γ ⊢check A ⇒ R; Γ ⊢check B               *)
(*R; A::Γ ⊢check[p] A ⇒ R; Γ ⊢check[regulator_theory_deduction_transform(A,p)]*)
(*                                    A→A                                     *)
(*R; A::Γ ⊢check[p] ⊥ ⇒ R; Γ ⊢check[regulator_theory_reductio_transform(A,p)] *)
(*                                     ¬A                                     *)
(*raw_reductio_certificate_check_bool(make_raw_reductio_certificate(profile,FT,Γ,A,p))=true*)

Definition sanity_mp_context : Context :=
  ctx_extend sanity_A
    (ctx_extend sanity_implication ctx_empty).

Definition sanity_mp_forward_proof : Proof :=
  cons (pl_assumption sanity_A)
  (cons (pl_assumption sanity_implication)
  (cons (pl_mp sanity_B 0 1)
  nil)).

Definition sanity_mp_reverse_proof : Proof :=
  cons (pl_assumption sanity_A)
  (cons (pl_assumption sanity_implication)
  (cons (pl_mp sanity_B 1 0)
  nil)).

Example sanity_mp_forward_checks :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    sanity_mp_context
    sanity_mp_forward_proof
    sanity_B = true.
Proof.
  reflexivity.
Qed.

Example sanity_mp_reverse_checks :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    sanity_mp_context
    sanity_mp_reverse_proof
    sanity_B = true.
Proof.
  reflexivity.
Qed.

Example sanity_bad_mp_rejected :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    (ctx_extend sanity_A ctx_empty)
    (cons (pl_assumption sanity_A)
      (cons (pl_mp sanity_B 0 1) nil))
    sanity_B = false.
Proof.
  reflexivity.
Qed.

Example sanity_deduction_transform_checks :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    ctx_empty
    (regulator_theory_deduction_transform
      sanity_A
      (sanity_assumption_proof sanity_A))
    (Imp sanity_A sanity_A) = true.
Proof.
  apply regulator_theory_deduction_checked.
  exact sanity_assumption_line_checks.
Qed.

Definition sanity_reductio_gamma : Context :=
  ctx_extend (Imp sanity_A Bot) ctx_empty.

Definition sanity_contradiction_context : Context :=
  ctx_extend sanity_A sanity_reductio_gamma.

Definition sanity_contradiction_proof : Proof :=
  cons (pl_assumption sanity_A)
  (cons (pl_assumption (Imp sanity_A Bot))
  (cons (pl_mp Bot 0 1)
  nil)).

Example sanity_contradiction_checks :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    sanity_contradiction_context
    sanity_contradiction_proof
    Bot = true.
Proof.
  reflexivity.
Qed.

Example sanity_reductio_transform_checks :
  regulator_theory_check_bool
    regulator_theory_empty_minimal
    sanity_reductio_gamma
    (regulator_theory_reductio_transform
      sanity_A
      sanity_contradiction_proof)
    (formula_negation sanity_A) = true.
Proof.
  apply regulator_theory_reductio_checked.
  exact sanity_contradiction_checks.
Qed.

Example sanity_raw_reductio_certificate_checks :
  raw_reductio_certificate_check_bool
    (make_raw_reductio_certificate
      regulator_profile_minimal
      finite_axiom_set_empty
      sanity_reductio_gamma
      sanity_A
      sanity_contradiction_proof) = true.
Proof.
  apply make_raw_reductio_certificate_checked.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          DERIVABILITY AND ADEQUACY                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The checked, inductive, and closure views coincide through the public
  adequacy lemmas. These examples are shape probes: they keep the exported
  theorem statements aligned with the current naming discipline.

(*                           A ∈ Γ ⇒ R; Γ ⊢check A                            *)
(*                         R; Γ ⊢check A ⇔ R; Γ ⊢ᵢ A                          *)
(*              R; Γ ⊢check A→B ∧ R; Γ ⊢check A ⇒ R; Γ ⊢check B               *)
(*              R; Γ ⊢check A→B ∧ R; Γ ⊬check B ⇒ R; Γ ⊬check A               *)
(*                  Γ ≤ctx Δ ∧ R; Γ ⊢check A ⇒ R; Δ ⊢check A                  *)

Example sanity_checked_derivable_assumption :
  regulator_theory_checked_derivable
    regulator_theory_empty_minimal
    (ctx_extend sanity_A ctx_empty)
    sanity_A.
Proof.
  apply regulator_theory_assumption_checked_derivable_lemma.
  reflexivity.
Qed.

Example sanity_inductive_derivable_assumption :
  regulator_theory_inductive_derivable
    regulator_theory_empty_minimal
    (ctx_extend sanity_A ctx_empty)
    sanity_A.
Proof.
  apply regulator_theory_checked_derivable_implies_inductive_lemma.
  exact sanity_checked_derivable_assumption.
Qed.

Example sanity_syntactic_adequacy_shape :
  forall R Gamma A,
    regulator_theory_checked_derivable R Gamma A <->
    regulator_theory_inductive_derivable R Gamma A.
Proof.
  exact regulator_theory_syntactic_adequacy_lemma.
Qed.

Example sanity_checked_derivable_mp :
  regulator_theory_checked_derivable
    regulator_theory_empty_minimal
    sanity_mp_context
    sanity_B.
Proof.
  apply regulator_theory_checked_derivable_mp_lemma
    with (A := sanity_A).
  - apply regulator_theory_assumption_checked_derivable_lemma.
    reflexivity.
  - apply regulator_theory_assumption_checked_derivable_lemma.
    reflexivity.
Qed.

Example sanity_negative_precomposition_shape :
  forall R Gamma A B,
    regulator_theory_checked_derivable R Gamma (Imp A B) ->
    regulator_theory_not_checked_derivable R Gamma B ->
    regulator_theory_not_checked_derivable R Gamma A.
Proof.
  exact regulator_theory_not_checked_derivable_precompose_lemma.
Qed.

Example sanity_context_monotone_shape :
  forall R Gamma Delta A,
    context_included Gamma Delta ->
    regulator_theory_checked_derivable R Gamma A ->
    regulator_theory_checked_derivable R Delta A.
Proof.
  exact regulator_theory_checked_derivable_context_monotone_lemma.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                     SYMBOLIC REGULATOR AND MACHINE VIEW                      │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The symbolic-regulator and machine views are transparent wrappers around
  the checker. These probes fix the definitional bridge from accepted proof
  scripts to symbolic-regulator derivability and to the closure predicate.

(* symbolic_regulator_derivable(regulator_theory_symbolic_regulator(R,Γ),A) ⇔ *)
(*                               R; Γ ⊢check A                                *)
(*  regulator_theory_machine(R,Γ,p,A) = regulator_theory_check_bool(R,Γ,p,A)  *)
(*                  regulator_theory_machine(R,Γ,p,A)=true ⇔                  *)
(*symbolic_regulator_accepts_bool(regulator_theory_symbolic_regulator(R,Γ),p,A)=true*)
(*                     regulator_theory_closure(R,Γ,A) ⇔                      *)
(*  symbolic_regulator_derivable(regulator_theory_symbolic_regulator(R,Γ),A)  *)

Example sanity_symbolic_derivable_iff_checked :
  forall R Gamma A,
    symbolic_regulator_derivable
      (regulator_theory_symbolic_regulator R Gamma)
      A
    <->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  exact regulator_theory_symbolic_derivable_iff_checked_derivable_lemma.
Qed.

Example sanity_machine_runs_checker :
  forall R Gamma p A,
    regulator_theory_machine R Gamma p A =
    regulator_theory_check_bool R Gamma p A.
Proof.
  exact regulator_theory_machine_runs_checker_lemma.
Qed.

Example sanity_machine_acceptance_iff_symbolic :
  forall R Gamma p A,
    regulator_theory_machine R Gamma p A = true
    <->
    symbolic_regulator_accepts_bool
      (regulator_theory_symbolic_regulator R Gamma)
      p A = true.
Proof.
  exact regulator_theory_machine_acceptance_iff_symbolic_regulator_lemma.
Qed.

Example sanity_closure_iff_symbolic_derivable :
  forall R Gamma A,
    regulator_theory_closure R Gamma A
    <->
    symbolic_regulator_derivable
      (regulator_theory_symbolic_regulator R Gamma)
      A.
Proof.
  exact regulator_theory_closure_iff_symbolic_derivable_lemma.
Qed.

Example sanity_machine_accepts_K_axiom :
  regulator_theory_machine
    regulator_theory_empty_minimal
    ctx_empty
    sanity_K_proof
    sanity_K_formula = true.
Proof.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              EVALUATION CLOSURE                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

  The evaluation-closure probes keep the generic and regulator-facing
  fixed-point engines visible from the public API. They do not instantiate a
  semantic evaluator; they only assert the exported theorem shapes.

(*           evaluation_complete(E) ⇒ evaluation_has_fixed_point(g)           *)
(*               evaluation_fixed_point_free(formula_negation)                *)
(*                   regulator_evaluation_complete(E) ⇒ ∃B.                   *)
(*                  regulator_theory_equivalent(R,Γ,B,g(B))                   *)

Example sanity_evaluation_frame_fixed_point_shape :
  forall Code Output
      (E : EvaluationFrame Code Output)
      (g : Output -> Output),
    evaluation_has_fixed_point g.
Proof.
  exact evaluation_frame_fixed_point_lemma.
Qed.

Example sanity_formula_negation_fixed_point_free :
  evaluation_fixed_point_free formula_negation.
Proof.
  exact formula_negation_fixed_point_free_lemma.
Qed.

Example sanity_regulator_evaluation_fixed_point_shape :
  forall R Gamma Code
      (E : RegulatorEvaluationFrame R Gamma Code)
      (g : Formula -> Formula),
    exists B : Formula,
      regulator_theory_equivalent R Gamma B (g B).
Proof.
  exact regulator_evaluation_frame_fixed_point_lemma.
Qed.
