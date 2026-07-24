(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Structural monotonicity for regulator theories.  A checked
script remains checked when its context is enlarged or when its available
axiom source is enlarged.  The proofs preserve the concrete script; the
existential checked-derivability forms are immediate corollaries.]]@*)

(*@head.end@*)

From M001 Require Export M001_06__Syntactic_Adequacy.

(*@section@[[CONTEXT MONOTONICITY]]@*)

(*@inline@[[`context_included Γ Δ` is syntactic Boolean inclusion of assumptions: every formula recognized by `ctx_mem_bool` in `Γ` is also recognized in `Δ`. This matches the Boolean membership test used to validate assumption lines.]]@*)

(*@unicodemath@[[Γ ≤ctx Δ  ≔  ∀A. ctx_mem_bool(A,Γ)=true ⇒ ctx_mem_bool(A,Δ)=true]]@*)

Definition context_included
    (Gamma Delta : Context) : Prop :=
  forall A,
    ctx_mem_bool A Gamma = true ->
    ctx_mem_bool A Delta = true.

(*@inline@[[The line-level context monotonicity proof only changes assumption lines. Axiom lines depend on the same regulator theory, and MP lines depend on the same checked prefix and formula indices, so those branches are definitionally unchanged.]]@*)

Lemma proof_line_valid_bool_context_monotone_lemma :
  forall R Gamma Delta prefix line,
    context_included Gamma Delta ->
    proof_line_valid_bool R Gamma prefix line = true ->
    proof_line_valid_bool R Delta prefix line = true.
Proof.
  intros R Gamma Delta prefix line Hinc Hline.
  destruct line as [phi just].
  destruct just as [| |i j].
  - unfold proof_line_valid_bool in *.
    simpl in *.
    apply Hinc.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
Qed.

Lemma proof_script_check_from_bool_context_monotone_lemma :
  forall R Gamma Delta prefix p,
    context_included Gamma Delta ->
    proof_script_check_from_bool R Gamma prefix p = true ->
    proof_script_check_from_bool R Delta prefix p = true.
Proof.
  intros R Gamma Delta prefix p Hinc.
  revert prefix.
  induction p as [|line rest IH]; intros prefix Hcheck.
  - reflexivity.
  - simpl in Hcheck.
    pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hline.
    pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hrest.
    simpl.
    rewrite
      (proof_line_valid_bool_context_monotone_lemma
        R Gamma Delta prefix line Hinc Hline).
    simpl.
    apply IH.
    exact Hrest.
Qed.

(*@inline@[[Full checker monotonicity preserves the same finite proof script. Only the line-checking conjunct is transported from `Γ` to `Δ`; the final-formula comparison is independent of the context.]]@*)

(*@unicodemath@[[Γ ≤ctx Δ  ∧  R; Γ ⊢check[p] A  ⇒  R; Δ ⊢check[p] A]]@*)

Lemma regulator_theory_check_bool_context_monotone_lemma :
  forall R Gamma Delta p A,
    context_included Gamma Delta ->
    regulator_theory_check_bool R Gamma p A = true ->
    regulator_theory_check_bool R Delta p A = true.
Proof.
  intros R Gamma Delta p A Hinc Hcheck.
  unfold regulator_theory_check_bool in *.
  pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hlines.
  pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hlast.
  rewrite
    (proof_script_check_from_bool_context_monotone_lemma
      R Gamma Delta nil p Hinc Hlines).
  simpl.
  exact Hlast.
Qed.

(*@unicodemath@[[Γ ≤ctx Δ  ∧  R; Γ ⊢check A  ⇒  R; Δ ⊢check A]]@*)

Lemma regulator_theory_checked_derivable_context_monotone_lemma :
  forall R Gamma Delta A,
    context_included Gamma Delta ->
    regulator_theory_checked_derivable R Gamma A ->
    regulator_theory_checked_derivable R Delta A.
Proof.
  intros R Gamma Delta A Hinc Hder.
  destruct Hder as [p Hp].
  exists p.
  apply regulator_theory_check_bool_context_monotone_lemma
    with (Gamma := Gamma).
  - exact Hinc.
  - exact Hp.
Qed.

(*@section@[[AXIOM-SET AND REGULATOR-THEORY MONOTONICITY]]@*)

(*@inline@[[`regulator_theory_included R S` is pointwise inclusion of the
available formula axioms after profile and external axiom source have been
combined.  It is the monotonicity hypothesis required by checked scripts.]]@*)

(*@unicodemath@[[R ≤rt S  ≔  ∀A. available_axiom_bool(R,A)=true ⇒ available_axiom_bool(S,A)=true]]@*)

Definition regulator_theory_included
    (R S : RegulatorTheory) : Prop :=
  forall A,
    available_axiom_bool R A = true ->
    available_axiom_bool S A = true.

(*@inline@[[Regulator-theory monotonicity changes only axiom lines. Assumption and MP validation are independent of the regulator-theory axiom source once the context and prefix are fixed.]]@*)

Lemma proof_line_valid_bool_regulator_theory_monotone_lemma :
  forall R S Gamma prefix line,
    regulator_theory_included R S ->
    proof_line_valid_bool R Gamma prefix line = true ->
    proof_line_valid_bool S Gamma prefix line = true.
Proof.
  intros R S Gamma prefix line Hinc Hline.
  destruct line as [phi just].
  destruct just as [| |i j].
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    apply Hinc.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
Qed.

Lemma proof_script_check_from_bool_regulator_theory_monotone_lemma :
  forall R S Gamma prefix p,
    regulator_theory_included R S ->
    proof_script_check_from_bool R Gamma prefix p = true ->
    proof_script_check_from_bool S Gamma prefix p = true.
Proof.
  intros R S Gamma prefix p Hinc.
  revert prefix.
  induction p as [|line rest IH]; intros prefix Hcheck.
  - reflexivity.
  - simpl in Hcheck.
    pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hline.
    pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hrest.
    simpl.
    rewrite
      (proof_line_valid_bool_regulator_theory_monotone_lemma
        R S Gamma prefix line Hinc Hline).
    simpl.
    apply IH.
    exact Hrest.
Qed.

(*@unicodemath@[[R ≤rt S  ∧  R; Γ ⊢check[p] A  ⇒  S; Γ ⊢check[p] A]]@*)

Lemma regulator_theory_check_bool_regulator_theory_monotone_lemma :
  forall R S Gamma p A,
    regulator_theory_included R S ->
    regulator_theory_check_bool R Gamma p A = true ->
    regulator_theory_check_bool S Gamma p A = true.
Proof.
  intros R S Gamma p A Hinc Hcheck.
  unfold regulator_theory_check_bool in *.
  pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hlines.
  pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hlast.
  rewrite
    (proof_script_check_from_bool_regulator_theory_monotone_lemma
      R S Gamma nil p Hinc Hlines).
  simpl.
  exact Hlast.
Qed.

(*@unicodemath@[[R ≤rt S  ∧  R; Γ ⊢check A  ⇒  S; Γ ⊢check A]]@*)

Lemma regulator_theory_checked_derivable_regulator_theory_monotone_lemma :
  forall R S Gamma A,
    regulator_theory_included R S ->
    regulator_theory_checked_derivable R Gamma A ->
    regulator_theory_checked_derivable S Gamma A.
Proof.
  intros R S Gamma A Hinc Hder.
  destruct Hder as [p Hp].
  exists p.
  apply regulator_theory_check_bool_regulator_theory_monotone_lemma
    with (R := R).
  - exact Hinc.
  - exact Hp.
Qed.
