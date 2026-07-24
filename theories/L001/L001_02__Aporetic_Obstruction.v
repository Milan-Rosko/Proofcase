(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Minimal obstruction layer: consistency turns the local collapse
into an explicit gap at the negation fixed point, local bivalence closes that
gap to contradiction, signed classification supplies its branch, membership
reaches it through refutation completeness, and negative-only refutation
remains inhabited.]]@*)

(*@head.end@*)

From L001 Require Export L001_01__Aporetic_Lemma.

(*@section@[[LOCAL OBSTRUCTION]]@*)

(*@inline@[[At a consistent negation fixed point, either accepted side would
supply a local branch and hence accepted bottom.  Both sides are therefore
excluded separately.]]@*)

Theorem fixedpoint_gap :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    ClosureConsistent C ->
    NegationFixedPointFor C B ->
    ~ C B /\ ~ C (formula_negation B).
Proof.
  intros C B Hmp Hconsistent Hfixed.
  split.
  - intro HB.
    apply Hconsistent.
    apply (local_branch_collapse C B Hmp Hfixed).
    left.
    exact HB.
  - intro HnotB.
    apply Hconsistent.
    apply (local_branch_collapse C B Hmp Hfixed).
    right.
    exact HnotB.
Qed.

(*@inline@[[Local excluded middle contradicts the two sides of the fixed-point
gap.]]@*)

Theorem core_diagonal_obstruction :
  forall (C : Formula -> Prop) B,
    ClosureModusPonens C ->
    ClosureConsistent C ->
    NegationFixedPointFor C B ->
    ClosureLocalExcludedMiddle C B ->
    False.
Proof.
  intros C B Hmp Hconsistent Hfixed Hlocal.
  destruct (fixedpoint_gap C B Hmp Hconsistent Hfixed)
    as [Hnot_positive Hnot_negative].
  destruct Hlocal as [Hpositive | Hnegative].
  - exact (Hnot_positive Hpositive).
  - exact (Hnot_negative Hnegative).
Qed.

(*@section@[[CLASSIFICATION OBSTRUCTIONS]]@*)

(*@inline@[[A signed classifier supplies exactly the local branch needed at a
given negation fixed point.  No evaluation premise is used here.]]@*)

Theorem local_signed_obstruction :
  forall (C : Formula -> Prop) B,
    ClosureConsistent C ->
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    ClosureSignedClassification C ->
    False.
Proof.
  intros C B Hconsistent Hmp Hfixed D.
  apply (core_diagonal_obstruction C B Hmp Hconsistent Hfixed).
  destruct (signed_classify D B) eqn:Hclassify.
  - left.
    exact (signed_true D B Hclassify).
  - right.
    exact (signed_false D B Hclassify).
Qed.

(*@inline@[[Membership decision reaches the same obstruction only after
refutation completeness converts its negative result into an accepted
object-language negation.]]@*)

Theorem local_membership_obstruction :
  forall (C : Formula -> Prop) B,
    ClosureConsistent C ->
    ClosureModusPonens C ->
    NegationFixedPointFor C B ->
    ClosureRefutationComplete C ->
    ClosureMembershipDecision C ->
    False.
Proof.
  intros C B Hconsistent Hmp Hfixed Hrefutation D.
  exact
    (local_signed_obstruction
       C B Hconsistent Hmp Hfixed
       (membership_to_signed C Hrefutation D)).
Qed.

(*@section@[[REFUTATION]]@*)

(*@inline@[[Negative-only refutation places no obligation on a false verdict.
The always-false function therefore inhabits it for every closure predicate.]]@*)

Theorem closure_refutation_inhabited :
  forall C : Formula -> Prop,
    exists r : Formula -> bool,
      (forall A, r A = false) /\
      (forall A, r A = true -> C (formula_negation A)).
Proof.
  intro C.
  exists (fun _ => false).
  split.
  - intro A.
    reflexivity.
  - intros A Htrue.
    discriminate Htrue.
Qed.
