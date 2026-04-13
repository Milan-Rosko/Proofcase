(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This phase introduces only the single-equation quartic target language needed for Step B of the roadmap. No family collapse is performed here; the file fixes the atomic degree-4 syntax, its semantics over valuations, and the associated yes-predicate.]]@*)

(*@head.end@*)

From P002 Require Export P002_11__Quadratic_Family.

Inductive monomial4 : Type :=
| m4_const
| m4_linear (i : nat)
| m4_quadratic (i j : nat)
| m4_cubic (i j k : nat)
| m4_quartic (i j k l : nat).

Record term4 : Type := {
  coeff4 : nat;
  mono4 : monomial4
}.

Record h10_nd4n_equation : Type := {
  var_count4 : nat;
  lhs_terms4 : list term4;
  rhs_terms4 : list term4
}.

Definition h10_nd4n_instance : Type := h10_nd4n_equation.

Definition monomial4_wf (n : nat) (m : monomial4) : Prop :=
  match m with
  | m4_const => True
  | m4_linear i => i < n
  | m4_quadratic i j => i < n /\ j < n
  | m4_cubic i j k => i < n /\ j < n /\ k < n
  | m4_quartic i j k l => i < n /\ j < n /\ k < n /\ l < n
  end.

Definition equation4_wf (eqn : h10_nd4n_equation) : Prop :=
  Forall (fun t => monomial4_wf (var_count4 eqn) (mono4 t)) (lhs_terms4 eqn) /\
  Forall (fun t => monomial4_wf (var_count4 eqn) (mono4 t)) (rhs_terms4 eqn).

Definition eval_monomial4 (rho : valuation) (m : monomial4) : nat :=
  match m with
  | m4_const => 1
  | m4_linear i => rho i
  | m4_quadratic i j => rho i * rho j
  | m4_cubic i j k => rho i * rho j * rho k
  | m4_quartic i j k l => rho i * rho j * rho k * rho l
  end.

Definition eval_term4 (rho : valuation) (t : term4) : nat :=
  coeff4 t * eval_monomial4 rho (mono4 t).

Definition eval_poly4 (ts : list term4) (rho : valuation) : nat :=
  fold_right (fun t acc => eval_term4 rho t + acc)%nat 0 ts.

Definition solves4 (eqn : h10_nd4n_equation) (rho : valuation) : Prop :=
  equation4_wf eqn /\
  eval_poly4 (lhs_terms4 eqn) rho = eval_poly4 (rhs_terms4 eqn) rho.

Definition h10_nd4n_yes (eqn : h10_nd4n_equation) : Prop :=
  exists rho : valuation, solves4 eqn rho.

Definition decides_h10_nd4n (solver : h10_nd4n_equation -> bool) : Prop :=
  decides h10_nd4n_yes solver.

Definition h10_nd4n_semantic_undecidable : Prop :=
  forall solver : h10_nd4n_equation -> bool,
    ~ decides_h10_nd4n solver.
