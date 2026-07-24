(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Small compile-time probes for the retained M001 boundary.  The
examples exercise the checker, finite checker, three proof transformations,
syntactic adequacy, structural monotonicity, and the generic symbolic
regulator.  They introduce no additional public interface.]]@*)

(*@head.end@*)

From M001 Require Import M001_95_API.

Definition sanity_axioms : AxiomSet :=
  {| axiom_set_contains_bool := fun _ => false |}.

Definition sanity_more_axioms : AxiomSet :=
  {| axiom_set_contains_bool := fun _ => true |}.

Definition sanity_theory : RegulatorTheory :=
  regulator_theory_with_axiom_set
    regulator_profile_minimal sanity_axioms.

Definition sanity_more_theory : RegulatorTheory :=
  regulator_theory_with_axiom_set
    regulator_profile_minimal sanity_more_axioms.

Definition sanity_finite_axioms : FiniteAxiomSet :=
  {| finite_axiom_set_formulas := nil |}.

Definition sanity_A : Formula := Imp Bot Bot.
Definition sanity_B : Formula := Imp sanity_A sanity_A.

Definition sanity_assumption (A : Formula) : Proof :=
  cons (pl_assumption A) nil.

(*@section@[[SYNTAX AND CHECKING]]@*)

Example sanity_not_self_negation :
  sanity_A <> formula_negation sanity_A.
Proof.
  apply formula_not_self_negation.
Qed.

Example sanity_assumption_checks :
  regulator_theory_check_bool
    sanity_theory
    (cons sanity_A nil)
    (sanity_assumption sanity_A)
    sanity_A = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example sanity_finite_checker :
  finite_axiom_set_check_bool
    regulator_profile_minimal
    sanity_finite_axioms
    (cons sanity_A nil)
    (sanity_assumption sanity_A)
    sanity_A = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(*@section@[[PROOF TRANSFORMATIONS]]@*)

Example sanity_deduction_transform :
  regulator_theory_check_bool
    sanity_theory nil
    (regulator_theory_deduction_transform
      sanity_A (sanity_assumption sanity_A))
    (Imp sanity_A sanity_A) = true.
Proof.
  apply regulator_theory_deduction_checked.
  vm_compute.
  reflexivity.
Qed.

Example sanity_reductio_transform :
  regulator_theory_check_bool
    sanity_theory nil
    (regulator_theory_reductio_transform
      Bot (sanity_assumption Bot))
    (formula_negation Bot) = true.
Proof.
  apply regulator_theory_reductio_checked.
  vm_compute.
  reflexivity.
Qed.

Example sanity_mp_composition :
  regulator_theory_check_bool
    sanity_theory
    (cons (Imp sanity_A sanity_B) (cons sanity_A nil))
    (regulator_theory_mp_compose
      sanity_B
      (sanity_assumption (Imp sanity_A sanity_B))
      (sanity_assumption sanity_A))
    sanity_B = true.
Proof.
  apply regulator_theory_mp_compose_checked_lemma
    with (A := sanity_A).
  - vm_compute.
    reflexivity.
  - vm_compute.
    reflexivity.
Qed.

(*@section@[[ADEQUACY AND MONOTONICITY]]@*)

Example sanity_adequacy :
  forall R Gamma A,
    regulator_theory_checked_derivable R Gamma A <->
    regulator_theory_inductive_derivable R Gamma A.
Proof.
  exact regulator_theory_syntactic_adequacy_lemma.
Qed.

Example sanity_context_monotonicity :
  regulator_theory_check_bool
    sanity_theory
    (cons sanity_A nil)
    (sanity_assumption sanity_A)
    sanity_A = true ->
  regulator_theory_check_bool
    sanity_theory
    (cons sanity_B (cons sanity_A nil))
    (sanity_assumption sanity_A)
    sanity_A = true.
Proof.
  intro Hcheck.
  apply regulator_theory_check_bool_context_monotone_lemma
    with (Gamma := cons sanity_A nil).
  - unfold context_included.
    intros A Hmem.
    exact
      (ctx_mem_bool_extend_preserve_lemma
        A sanity_B (cons sanity_A nil) Hmem).
  - exact Hcheck.
Qed.

Lemma sanity_theory_included :
  regulator_theory_included sanity_theory sanity_more_theory.
Proof.
  intros A _.
  unfold sanity_more_theory,
    sanity_more_axioms,
    regulator_theory_with_axiom_set,
    available_axiom_bool.
  simpl.
  rewrite orb_true_r.
  reflexivity.
Qed.

Example sanity_theory_monotonicity :
  regulator_theory_check_bool
    sanity_theory
    (cons sanity_A nil)
    (sanity_assumption sanity_A)
    sanity_A = true ->
  regulator_theory_check_bool
    sanity_more_theory
    (cons sanity_A nil)
    (sanity_assumption sanity_A)
    sanity_A = true.
Proof.
  apply regulator_theory_check_bool_regulator_theory_monotone_lemma.
  exact sanity_theory_included.
Qed.

(*@section@[[SYMBOLIC REGULATOR]]@*)

Definition sanity_symbolic_regulator : S_λ :=
  regulator_theory_symbolic_regulator
    sanity_theory (cons sanity_A nil).

Example sanity_symbolic_acceptance :
  symbolic_regulator_derivable sanity_symbolic_regulator sanity_A.
Proof.
  exists (sanity_assumption sanity_A).
  vm_compute.
  reflexivity.
Qed.

Example sanity_symbolic_release :
  symbolic_regulator_release
    sanity_symbolic_regulator
    (sanity_assumption sanity_A)
    sanity_A = Some sanity_A.
Proof.
  apply symbolic_regulator_release_complete.
  vm_compute.
  reflexivity.
Qed.

Example sanity_symbolic_release_bridge :
  regulator_theory_checked_derivable
    sanity_theory (cons sanity_A nil) sanity_A <->
  exists p : Proof,
    symbolic_regulator_release
      sanity_symbolic_regulator p sanity_A = Some sanity_A.
Proof.
  exact
    (regulator_theory_symbolic_regulator_release_iff
       sanity_theory (cons sanity_A nil) sanity_A).
Qed.
