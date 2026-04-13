(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This layer imports the proved D001 observation algebra for one Fibonacci-machine step and packages selector-gated cubic equations for the atomic transition constraints.]]@*)

(*@doc.pl@[[The equations here do not yet aggregate a full step. They provide the reusable cubic atoms that the later compiler layer will combine.]]@*)

(*@head.end@*)

From P002 Require Export P002_06__Trace_Witness.

Definition SourceState : EncodedState -> MachineState := source_state.
Definition TargetState : EncodedState -> MachineState := target_state.

Definition ip_matches_b (q : nat) (s : EncodedState) : bool := ip_eqb q s.
Definition counter_zero_obs_b (c : MachineCounter) (s : EncodedState) : bool :=
  counter_zero_b c s.
Definition target_ip_matches_b (q : nat) (t : EncodedState) : bool :=
  target_ipb q t.
Definition counter_succ_obs_b
    (c : MachineCounter) (s t : EncodedState) : bool :=
  counter_succ_b c s t.
Definition counter_pred_obs_b
    (c : MachineCounter) (s t : EncodedState) : bool :=
  counter_pred_b c s t.
Definition frozen_other_counter_obs_b
    (c : MachineCounter) (s t : EncodedState) : bool :=
  frozen_other_counter_b c s t.

Definition selector_var_wf (selector x : nat) : nat :=
  S (Nat.max selector x).

Definition selector_binary_var_wf (selector x y : nat) : nat :=
  S (Nat.max selector (Nat.max x y)).

Definition emit_selector_zero_eq (selector x : nat) : h10_nd3n_equation :=
  {|
    var_count := selector_var_wf selector x;
    lhs_terms := [{| coeff := 1; mono := m_quadratic selector x |}];
    rhs_terms := []
  |}.

Definition emit_selector_same_eq (selector x y : nat) : h10_nd3n_equation :=
  {|
    var_count := selector_binary_var_wf selector x y;
    lhs_terms := [{| coeff := 1; mono := m_quadratic selector x |}];
    rhs_terms := [{| coeff := 1; mono := m_quadratic selector y |}]
  |}.

Definition emit_selector_succ_eq (selector target source : nat)
  : h10_nd3n_equation :=
  {|
    var_count := selector_binary_var_wf selector target source;
    lhs_terms := [{| coeff := 1; mono := m_quadratic selector target |}];
    rhs_terms :=
      [{| coeff := 1; mono := m_linear selector |};
       {| coeff := 1; mono := m_quadratic selector source |}]
  |}.

Definition emit_selector_pred_eq (selector source target : nat)
  : h10_nd3n_equation :=
  emit_selector_succ_eq selector source target.

Definition emit_selector_product_zero_eq (selector x y : nat)
  : h10_nd3n_equation :=
  {|
    var_count := selector_binary_var_wf selector x y;
    lhs_terms := [{| coeff := 1; mono := m_cubic selector x y |}];
    rhs_terms := []
  |}.

(*@inline@[[The selector emitters are the basic cubic atoms of the FM compiler. They do not yet choose a branch by themselves; instead they express “if the selector is active, then the guarded relation must hold”, while later layers add the selector-booleanity and exclusivity constraints.]]@*)
(*@unicodemath@[[a\cdot x = 0,\quad a\cdot x = a\cdot y,\quad a\cdot t = a + a\cdot s,\quad a\cdot x\cdot y = 0.]]@*)

Lemma eval_poly_singleton_term :
  forall (t : term) (rho : valuation),
    eval_poly [t] rho = eval_term rho t.
Proof.
  intros t rho.
  unfold eval_poly.
  simpl.
  lia.
Qed.

Lemma emit_selector_zero_eq_wf :
  forall selector x,
    equation_wf (emit_selector_zero_eq selector x).
Proof.
  intros selector x.
  unfold emit_selector_zero_eq, equation_wf, selector_var_wf.
  split.
  - constructor.
    + simpl.
      split; apply Nat.lt_succ_r; apply Nat.le_max_l || apply Nat.le_max_r.
    + constructor.
  - constructor.
Qed.

Lemma emit_selector_same_eq_wf :
  forall selector x y,
    equation_wf (emit_selector_same_eq selector x y).
Proof.
  intros selector x y.
  unfold emit_selector_same_eq, equation_wf, selector_binary_var_wf.
  split.
  - constructor.
    + simpl.
      split.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_l.
      * apply Nat.lt_succ_r.
        apply Nat.le_trans with (m := Nat.max x y).
        -- apply Nat.le_max_l.
        -- apply Nat.le_max_r.
    + constructor.
  - constructor.
    + simpl.
      split.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_l.
      * apply Nat.lt_succ_r.
        apply Nat.le_trans with (m := Nat.max x y).
        -- apply Nat.le_max_r.
        -- apply Nat.le_max_r.
    + constructor.
Qed.

Lemma emit_selector_succ_eq_wf :
  forall selector target source,
    equation_wf (emit_selector_succ_eq selector target source).
Proof.
  intros selector target source.
  unfold emit_selector_succ_eq, equation_wf, selector_binary_var_wf.
  split.
  - constructor.
    + simpl.
      split.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_l.
      * apply Nat.lt_succ_r.
        apply Nat.le_trans with (m := Nat.max target source).
        -- apply Nat.le_max_l.
        -- apply Nat.le_max_r.
    + constructor.
  - constructor.
    + simpl.
      apply Nat.lt_succ_r.
      apply Nat.le_max_l.
    + constructor.
      * simpl.
        split.
        -- apply Nat.lt_succ_r.
           apply Nat.le_max_l.
        -- apply Nat.lt_succ_r.
           apply Nat.le_trans with (m := Nat.max target source).
           ++ apply Nat.le_max_r.
           ++ apply Nat.le_max_r.
      * constructor.
Qed.

Lemma emit_selector_product_zero_eq_wf :
  forall selector x y,
    equation_wf (emit_selector_product_zero_eq selector x y).
Proof.
  intros selector x y.
  unfold emit_selector_product_zero_eq, equation_wf, selector_binary_var_wf.
  split.
  - constructor.
    + simpl.
      repeat split.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_l.
      * apply Nat.lt_succ_r.
        apply Nat.le_trans with (m := Nat.max x y).
        -- apply Nat.le_max_l.
        -- apply Nat.le_max_r.
      * apply Nat.lt_succ_r.
        apply Nat.le_trans with (m := Nat.max x y).
        -- apply Nat.le_max_r.
        -- apply Nat.le_max_r.
    + constructor.
  - constructor.
Qed.

Lemma emit_selector_zero_eq_active :
  forall rho selector x,
    rho selector = 1 ->
    solves (emit_selector_zero_eq selector x) rho <->
    rho x = 0.
Proof.
  intros rho selector x Hsel.
  unfold solves, emit_selector_zero_eq.
  split.
  - intros [_ Hsol].
    unfold eval_poly, eval_term, eval_monomial in Hsol.
    simpl in Hsol.
    rewrite Hsel in Hsol.
    lia.
  - intros Hx.
    split.
    + apply emit_selector_zero_eq_wf.
    + unfold eval_poly, eval_term, eval_monomial.
      simpl.
      rewrite Hsel, Hx.
      lia.
Qed.

Lemma emit_selector_zero_eq_inactive :
  forall rho selector x,
    rho selector = 0 ->
    solves (emit_selector_zero_eq selector x) rho.
Proof.
  intros rho selector x Hsel.
  split.
  - apply emit_selector_zero_eq_wf.
  - unfold emit_selector_zero_eq, eval_poly, eval_term, eval_monomial.
    simpl.
    rewrite Hsel.
    lia.
Qed.

Lemma emit_selector_same_eq_active :
  forall rho selector x y,
    rho selector = 1 ->
    solves (emit_selector_same_eq selector x y) rho <->
    rho x = rho y.
Proof.
  intros rho selector x y Hsel.
  unfold solves, emit_selector_same_eq.
  split.
  - intros [_ Hsol].
    unfold eval_poly, eval_term, eval_monomial in Hsol.
    simpl in Hsol.
    rewrite Hsel in Hsol.
    lia.
  - intros Hxy.
    split.
    + apply emit_selector_same_eq_wf.
    + unfold eval_poly, eval_term, eval_monomial.
      simpl.
      rewrite Hsel, Hxy.
      lia.
Qed.

Lemma emit_selector_same_eq_inactive :
  forall rho selector x y,
    rho selector = 0 ->
    solves (emit_selector_same_eq selector x y) rho.
Proof.
  intros rho selector x y Hsel.
  split.
  - apply emit_selector_same_eq_wf.
  - unfold emit_selector_same_eq, eval_poly, eval_term, eval_monomial.
    simpl.
    rewrite Hsel.
    lia.
Qed.

Lemma emit_selector_succ_eq_active :
  forall rho selector target source,
    rho selector = 1 ->
    solves (emit_selector_succ_eq selector target source) rho <->
    rho target = S (rho source).
Proof.
  intros rho selector target source Hsel.
  unfold solves, emit_selector_succ_eq.
  split.
  - intros [_ Hsol].
    unfold eval_poly, eval_term, eval_monomial in Hsol.
    simpl in Hsol.
    rewrite Hsel in Hsol.
    lia.
  - intros Hsucc.
    split.
    + apply emit_selector_succ_eq_wf.
    + unfold eval_poly, eval_term, eval_monomial.
      simpl.
      rewrite Hsel, Hsucc.
      lia.
Qed.

Lemma emit_selector_succ_eq_inactive :
  forall rho selector target source,
    rho selector = 0 ->
    solves (emit_selector_succ_eq selector target source) rho.
Proof.
  intros rho selector target source Hsel.
  split.
  - apply emit_selector_succ_eq_wf.
  - unfold emit_selector_succ_eq, eval_poly, eval_term, eval_monomial.
    simpl.
    rewrite Hsel.
    lia.
Qed.

Lemma emit_selector_pred_eq_active :
  forall rho selector source target,
    rho selector = 1 ->
    solves (emit_selector_pred_eq selector source target) rho <->
    rho source = S (rho target).
Proof.
  exact emit_selector_succ_eq_active.
Qed.

Lemma emit_selector_product_zero_eq_active :
  forall rho selector x y,
    rho selector = 1 ->
    solves (emit_selector_product_zero_eq selector x y) rho <->
    (rho x = 0 \/ rho y = 0).
Proof.
  intros rho selector x y Hsel.
  unfold solves, emit_selector_product_zero_eq.
  split.
  - intros [_ Hsol].
    unfold eval_poly, eval_term, eval_monomial in Hsol.
    simpl in Hsol.
    rewrite Hsel in Hsol.
    assert (Hprod : rho x * rho y = 0) by lia.
    apply Nat.eq_mul_0 in Hprod.
    destruct Hprod as [Hx|Hy].
    + left. exact Hx.
    + right. exact Hy.
  - intros [Hx|Hy].
    + split.
      * apply emit_selector_product_zero_eq_wf.
      * unfold eval_poly, eval_term, eval_monomial.
        simpl.
        rewrite Hsel, Hx.
        lia.
    + split.
      * apply emit_selector_product_zero_eq_wf.
      * unfold eval_poly, eval_term, eval_monomial.
        simpl.
        rewrite Hsel, Hy.
        lia.
Qed.

Lemma emit_selector_product_zero_eq_inactive :
  forall rho selector x y,
    rho selector = 0 ->
    solves (emit_selector_product_zero_eq selector x y) rho.
Proof.
  intros rho selector x y Hsel.
  split.
  - apply emit_selector_product_zero_eq_wf.
  - unfold emit_selector_product_zero_eq, eval_poly, eval_term, eval_monomial.
    simpl.
    rewrite Hsel.
    lia.
Qed.

(*@inline@[[The active/inactive correctness lemmas are the semantic contract of the selector atoms. When the selector takes value `1`, the intended guarded arithmetic relation is enforced; when it takes value `0`, the corresponding equation becomes vacuous.]]@*)
(*@unicodemath@[[a=1 \Rightarrow solves(E\_{guarded},\rho)\Leftrightarrow\text{guarded relation},\qquad a=0 \Rightarrow solves(E\_{guarded},\rho).]]@*)

Lemma ip_matches_b_correct_bridge :
  forall q s,
    ip_matches_b q s = true <-> state_ip (decode_state s) = q.
Proof.
  exact ip_eqb_correct.
Qed.

Lemma counter_zero_obs_b_correct_bridge :
  forall c s,
    counter_zero_obs_b c s = true <->
    read_counter c (decode_state s) = 0.
Proof.
  exact counter_zero_b_correct.
Qed.

Lemma target_ip_matches_b_correct_bridge :
  forall q t,
    target_ip_matches_b q t = true <-> state_ip (decode_state t) = q.
Proof.
  exact target_ipb_correct.
Qed.

Lemma counter_succ_obs_b_correct_bridge :
  forall c s t,
    counter_succ_obs_b c s t = true <->
    read_counter c (decode_state t) =
    S (read_counter c (decode_state s)).
Proof.
  exact counter_succ_b_correct.
Qed.

Lemma counter_pred_obs_b_correct_bridge :
  forall c s t,
    counter_pred_obs_b c s t = true <->
    read_counter c (decode_state s) =
    S (read_counter c (decode_state t)).
Proof.
  exact counter_pred_b_correct.
Qed.

Lemma frozen_other_counter_obs_b_correct_bridge :
  forall c s t,
    frozen_other_counter_obs_b c s t = true <->
    match c with
    | Counter1 => state_r2 (decode_state s) = state_r2 (decode_state t)
    | Counter2 => state_r1 (decode_state s) = state_r1 (decode_state t)
    end.
Proof.
  exact frozen_other_counter_b_correct.
Qed.

Lemma NextState_additive_bridge :
  forall prog st,
    state_well_formed st ->
    Z.of_nat (StepCode prog (encode_state st)) =
    (Z.of_nat (encode_state st) +
     step_ip_delta prog st +
     step_register_delta prog st)%Z.
Proof.
  exact NextState_additive.
Qed.

Lemma HALT_additive_bridge :
  forall prog st,
    state_well_formed st ->
    fetch_instruction prog st = Some HALT ->
    Z.of_nat (StepCode prog (encode_state st)) =
    (Z.of_nat (encode_state st) + ip_delta (state_ip st) 0)%Z.
Proof.
  exact HALT_additive.
Qed.

(*@inline@[[The additive bridge theorems connect the local selector atoms back to the real FM dynamics. They say that on well-formed encoded states, one machine step changes the external code exactly by the instruction-pointer delta plus the register delta, with HALT collapsing to the IP-reset case.]]@*)
(*@unicodemath@[[StepCode(prog,\encode\_state(st)) = \encode\_state(st) + \Delta\_{IP}(prog,st) + \Delta\_{R}(prog,st)\ \text{(over }\mathbb Z\text{)}.]]@*)
