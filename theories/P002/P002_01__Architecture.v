(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This file is the unique concrete seam where the FM substrate enters P002.]]@*)

(*@doc.pl@[[Every later P002 layer should be judged only by whether it helps prove the family-level compiler theorem `compile_fm_family_correct`. The role of the present file is therefore narrow: freeze the concrete FM arithmetic interface imported from D001 and expose the smallest polynomial atoms that later family compilation lemmas consume.]]@*)

(*@head.end@*)

From P002 Require Export P002_00_Premises.
From D001 Require Export D001_07__Step_Arithmetization.
From Stdlib Require Export List Arith Lia Sorting.Permutation.

(*@inline@[[This is the only file in P002 allowed to import D001 directly. The membrane stops at the arithmetic/operational layer (`D001_07`): later compiler files may reuse syntax, codecs, step laws, trace coding, and additive deltas, but not acceptance or universality facts.]]@*)
(*@unicodemath@[[P002\_00 \to P002\_01 \to P002\_02 \to \cdots \to P002\_08,\qquad \text{with D001 entering only at }P002\_01.]]@*)

Definition FMCode : Type := nat.
Definition FMProgram : Type := program.
Definition FMEncodeState : FMState -> FMCode := encode_state.
Definition FMDecodeState : FMCode -> FMState := decode_state.
Definition FMNormalizeCode : FMCode -> FMCode := normalize_state_code.
Definition FMValidStateCode : FMCode -> Prop := valid_state_code.
Definition FMStep : FMProgram -> FMCode -> FMCode := NextState.
Definition FMTraceCode : list FMCode -> nat := encode_nat_list.
Definition FMRunTrace : (FMCode -> FMCode) -> nat -> FMCode -> list FMCode :=
  code_run_trace.
Definition FMRawTraceWitness
    : (FMCode -> FMCode) -> (FMCode -> Prop) -> FMCode -> nat -> Prop :=
  raw_trace_witness_from.

(*@inline@[[The `FM*` aliases exported here are intentionally arithmetic only. Acceptance and universality interfaces live later in `P002_98`, not in the compiler membrane.]]@*)
(*@unicodemath@[[FMCode=\mathbb N,\quad FMStep(prog,s)=NextState(prog,s),\quad FMValidStateCode(s)\Leftrightarrow normalize\_state\_code(s)=s.]]@*)

Theorem FM_valid_state_code_iff_fixed :
  forall s,
    FMValidStateCode s <-> FMNormalizeCode s = s.
Proof.
  exact valid_state_code_iff_fixed.
Qed.

(*@inline@[[`FM_valid_state_code_iff_fixed` is the image-characterization law exported by the membrane. It lets later P002 files recognize genuine FM state codes by a single normalization equation, without reopening the whole D001 codec.]]@*)
(*@unicodemath@[[FMValidStateCode(s)\Leftrightarrow FMNormalizeCode(s)=s.]]@*)

Theorem FM_decode_state_well_formed :
  forall s,
    state_well_formed (FMDecodeState s).
Proof.
  exact decode_state_well_formed.
Qed.

(*@inline@[[`FM_decode_state_well_formed` packages the total projection semantics of the FM codec: arbitrary raw naturals may be decoded safely because decoding always lands back inside the bounded FM state image.]]@*)

Theorem FM_stepb_correct :
  forall prog s t,
    stepb prog s t = true <-> t = FMStep prog s.
Proof.
  exact stepb_correct.
Qed.

Theorem FM_stepb_correct_of :
  forall L prog s t,
    stepb_of L prog s t = true <-> t = NextState_of L prog s.
Proof.
  exact stepb_correct_of.
Qed.

(*@inline@[[`FM_stepb_correct` and `FM_stepb_correct_of` are the executable graph laws for FM stepping. They turn the boolean one-step test into an exact equality characterization of the next code, both for the fixed machine and for the family-parametrized machine.]]@*)
(*@unicodemath@[[stepb(prog,s,t)=true\Leftrightarrow t=FMStep(prog,s),\qquad stepb\_of(L,prog,s,t)=true\Leftrightarrow t=NextState\_of(L,prog,s).]]@*)

Definition emit_boolean_constraint (i : nat) : h10_nd3n_equation :=
  {|
    var_count := S i;
    lhs_terms := [{| coeff := 1; mono := m_quadratic i i |}];
    rhs_terms := [{| coeff := 1; mono := m_linear i |}]
  |}.

Definition emit_non_adjacency_constraint (i j : nat) : h10_nd3n_equation :=
  {|
    var_count := S (Nat.max i j);
    lhs_terms := [{| coeff := 1; mono := m_quadratic i j |}];
    rhs_terms := []
  |}.

(*@inline@[[`emit_boolean_constraint` now emits the honest equation `x_i^2 = x_i`, and `emit_non_adjacency_constraint` emits the honest zero-product equation `x_i x_j = 0`. Both forms are chosen specifically because they are the atomic digit constraints that the later FM-to-family reduction reuses blockwise.]]@*)
(*@unicodemath@[[emit\_boolean\_constraint(i):\ x_i^2=x_i,\qquad emit\_non\_adjacency\_constraint(i,j):\ x_i x_j = 0.]]@*)

Lemma eval_poly_singleton :
  forall (t : term) (rho : valuation),
    eval_poly [t] rho = eval_term rho t.
Proof.
  intros t rho.
  unfold eval_poly.
  simpl.
  lia.
Qed.

(*@inline@[[`eval_poly_singleton` is the basic normalization lemma for one-term equations. The architecture file exports it because nearly every later correctness proof for atomic emitters starts by collapsing a singleton polynomial back to its underlying term.]]@*)

Lemma emit_boolean_constraint_wf :
  forall i,
    equation_wf (emit_boolean_constraint i).
Proof.
  intro i.
  unfold emit_boolean_constraint, equation_wf.
  split.
  - constructor.
    + simpl.
      split.
      * apply Nat.lt_succ_diag_r.
      * apply Nat.lt_succ_diag_r.
    + constructor.
  - constructor.
    + simpl.
      apply Nat.lt_succ_diag_r.
    + constructor.
Qed.

(*@inline@[[The well-formedness lemmas show that the first emitted FM atoms already satisfy the scoping discipline of `P002_00`. This matters because `solves` includes well-formedness by definition, so later semantic theorems rely on these obligations having been discharged here.]]@*)
(*@unicodemath@[[equation\_wf(emit\_boolean\_constraint(i)),\qquad equation\_wf(emit\_non\_adjacency\_constraint(i,j)).]]@*)

Lemma emit_non_adjacency_constraint_wf :
  forall i j,
    equation_wf (emit_non_adjacency_constraint i j).
Proof.
  intros i j.
  unfold emit_non_adjacency_constraint, equation_wf.
  split.
  - constructor.
    + simpl.
      split.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_l.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_r.
    + constructor.
  - constructor.
Qed.

Lemma nat_square_eq_self :
  forall n,
    n * n = n <-> n = 0 \/ n = 1.
Proof.
  intros n.
  split.
  - intro Hsq.
    destruct n as [|n].
    + left.
      reflexivity.
    + assert (Hmul : S n * S n = S n * 1).
      { replace (S n * 1) with (S n) by lia. exact Hsq. }
      apply Nat.mul_cancel_l in Hmul.
      * right.
        lia.
      * lia.
  - intros Hn.
    destruct Hn as [Hz|Ho].
    + subst.
      reflexivity.
    + subst.
      reflexivity.
Qed.

(*@inline@[[`nat_square_eq_self` is the elementary arithmetic fact that makes the boolean emitter work over ℕ. The membrane exports it explicitly so later layers can appeal to the intended meaning of `x^2=x` without reproving the arithmetic normalization each time.]]@*)
(*@unicodemath@[[n^2=n\Leftrightarrow n\in\{0,1\}.]]@*)

Lemma boolean_constraint_correct :
  forall (rho : valuation) (i : nat),
    solves (emit_boolean_constraint i) rho <->
    (rho i = 0 \/ rho i = 1).
Proof.
  intros rho i.
  unfold solves.
  split.
  - intros [_ Hsol].
    cbv [emit_boolean_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial]
      in Hsol.
    simpl in Hsol.
    repeat rewrite Nat.add_0_r in Hsol.
    apply nat_square_eq_self.
    exact Hsol.
  - intros Hbool.
    split.
    + apply emit_boolean_constraint_wf.
    + cbv [emit_boolean_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial].
      simpl.
      repeat rewrite Nat.add_0_r.
      apply nat_square_eq_self.
      exact Hbool.
Qed.

(*@inline@[[`boolean_constraint_correct` and `non_adjacency_correct` are the first soundness facts for P002’s arithmetic atoms. They certify that the emitted equations already say exactly what the later family-level compiler route intends them to say about FM digits, before any higher trace-family assembly is introduced.]]@*)

Lemma non_adjacency_correct :
  forall (rho : valuation) (i j : nat),
    solves (emit_non_adjacency_constraint i j) rho <->
    (rho i = 0 \/ rho j = 0).
Proof.
  intros rho i j.
  unfold emit_non_adjacency_constraint.
  split.
  - intros [_ Hsol].
    cbv [emit_non_adjacency_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial]
      in Hsol.
    simpl in Hsol.
    repeat rewrite Nat.add_0_r in Hsol.
    apply Nat.eq_mul_0.
    exact Hsol.
  - intros Hzero.
    split.
    + apply emit_non_adjacency_constraint_wf.
    + cbv [emit_non_adjacency_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial].
      simpl.
      repeat rewrite Nat.add_0_r.
      apply Nat.eq_mul_0.
      exact Hzero.
Qed.
