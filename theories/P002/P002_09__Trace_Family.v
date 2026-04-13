(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@inline@[[This file starts the honest family-level FM reduction. Its output is a finite cubic family whose satisfiability should mirror one FM trace witness exactly; there is no longer any family-to-single-equation compression step in scope.]]@*)

(*@head.end@*)

From P002 Require Export P002_08__Compiler.


Definition TraceConstraintFamily : Type := equation_family.

Definition FMFixedTracePayloadFrom
    (prog : MachineProgram) (start witness fuel : nat) : Prop :=
  witness =
    encode_code_trace
      (code_run_trace (StepCode prog) fuel start) /\
  halted_state
    (decode_state (code_run_last (StepCode prog) fuel start)).

Definition FMFixedTracePayload
    (prog : MachineProgram) (input witness fuel : nat) : Prop :=
  FMFixedTracePayloadFrom prog (start_code input) witness fuel.

Definition FMTraceSearchPayload
    (prog : MachineProgram) (input : nat) : Prop :=
  exists witness fuel,
    FMFixedTracePayload prog input witness fuel.

Definition trace_family_valuation
    (prog : MachineProgram) (input _witness fuel : nat) : valuation :=
  fun n =>
    match n with
    | 0 => code_run_last (StepCode prog) fuel (start_code input)
    | S t =>
        if Nat.leb t fuel
        then code_run_last (StepCode prog) t (start_code input)
        else 0
    end.

Definition trace_halt_var : nat := 0.

Definition trace_code_var (t : nat) : nat := S t.

Definition trace_channel_code (rho : valuation) (t : nat) : nat :=
  rho (trace_code_var t).

Definition trace_channel_halt_code (rho : valuation) : nat :=
  rho trace_halt_var.

(*@inline@[[`FMFixedTracePayloadFrom` is the general raw trace payload from an arbitrary start code. `FMFixedTracePayload` is the input-specialized version used by the public compiler route.]]@*)
(*@inline@[[`FMFixedTracePayload` is the exact fixed-witness semantic object that the trace-family emitter must mirror. It exposes the raw arithmetic payload of a valid witness: one fuel bound whose iterated `StepCode` trace encodes to the given witness and whose last code decodes to a halted state.]]@*)
(*@inline@[[`FMTraceSearchPayload` is the open existential version used by the family compiler: it internalizes both the witness code and the fuel bound into the valuation, while keeping compilation syntax-driven.]]@*)
(*@unicodemath@[[FMFixedTracePayload(prog,input,W,T)\;\equiv\;W=\encode\_code\_trace(code\_run\_trace(StepCode(prog),T,start\_code(input)))]][[\;\wedge\;halted\_state(decode\_state(code\_run\_last(StepCode(prog),T,start\_code(input)))).]]@*)
(*@inline@[[The fixed trace-channel indexing is now concrete. Variable `0` is reserved for the designated final halt code, and variable `S t` stores the code at time `t`.]]@*)

Definition trace_channels_match_run
    (prog : MachineProgram) (input witness : nat) (rho : valuation) : Prop :=
  exists fuel,
    witness =
      encode_code_trace
        (code_run_trace (StepCode prog) fuel (start_code input)) /\
    forall t,
      t <= fuel ->
      trace_channel_code rho t = code_trace_nth t witness.

Definition trace_channels_match_witness
    (_prog : MachineProgram) (_input witness : nat) (rho : valuation) : Prop :=
  forall t,
    t <= witness ->
    trace_channel_code rho t = code_trace_nth t witness.

Definition trace_channels_start
    (_prog : MachineProgram) (input witness : nat) (rho : valuation) : Prop :=
  trace_channel_code rho 0 = start_code input.

Definition step_channels_follow_StepCode
    (prog : MachineProgram) (input witness : nat) (rho : valuation) : Prop :=
  exists fuel,
    witness =
      encode_code_trace
        (code_run_trace (StepCode prog) fuel (start_code input)) /\
    forall t,
      t < fuel ->
      trace_channel_code rho (S t) =
      StepCode prog (trace_channel_code rho t).

Definition trace_channels_halt
    (prog : MachineProgram) (input witness : nat) (rho : valuation) : Prop :=
  exists fuel,
    witness =
      encode_code_trace
        (code_run_trace (StepCode prog) fuel (start_code input)) /\
    trace_channel_halt_code rho =
      code_run_last (StepCode prog) fuel (start_code input) /\
    halted_state (decode_state (trace_channel_halt_code rho)).

Definition trace_witness_length (witness : nat) : nat :=
  length (decode_code_trace witness).

Definition trace_witness_step_count (witness : nat) : nat :=
  Nat.pred (trace_witness_length witness).

Definition trace_witness_last_code (witness : nat) : nat :=
  code_trace_nth (trace_witness_step_count witness) witness.

Definition step_channels_follow_witness
    (prog : MachineProgram) (_input witness : nat) (rho : valuation) : Prop :=
  forall t,
    S t < trace_witness_length witness ->
    trace_channel_code rho (S t) =
    StepCode prog (code_trace_nth t witness).

Definition trace_witness_fixed (witness : nat) : Prop :=
  encode_code_trace (decode_code_trace witness) = witness.

Definition trace_channels_halt_witness
    (_prog : MachineProgram) (_input witness : nat) (rho : valuation) : Prop :=
  trace_channel_halt_code rho = trace_witness_last_code witness /\
  halted_state (decode_state (trace_channel_halt_code rho)).

(*@inline@[[The trace-channel predicates are the semantic shorthands that make the block theorems readable. They describe what the valuation is supposed to mean: a run-shaped sequence of code channels, the fixed start code at time `0`, local successor alignment with `StepCode`, and a designated final halted code.]]@*)
(*@unicodemath@[[trace\_channels\_match\_run(prog,input,W,\rho)\Rightarrow \forall t\le fuel,\ trace\_channel\_code(\rho,t)=coded\_nth(t,W).]]@*)

Definition emit_linear_const_equation (var value : nat) : h10_nd3n_equation :=
  {|
    var_count := S var;
    lhs_terms := [{| coeff := 1; mono := m_linear var |}];
    rhs_terms := [{| coeff := value; mono := m_const |}]
  |}.

Definition emit_false_equation : h10_nd3n_equation :=
  {|
    var_count := 0;
    lhs_terms := [{| coeff := 1; mono := m_const |}];
    rhs_terms := []
  |}.

Fixpoint emit_trace_shape_family_upto
    (witness bound : nat) : equation_family :=
  match bound with
  | 0 =>
      [emit_linear_const_equation (trace_code_var 0) (code_trace_nth 0 witness)]
  | S bound' =>
      emit_trace_shape_family_upto witness bound' ++
      [emit_linear_const_equation
         (trace_code_var (S bound'))
         (code_trace_nth (S bound') witness)]
  end.

Definition emit_trace_shape_family
    (_prog : MachineProgram) (_input witness : nat) : equation_family :=
  emit_trace_shape_family_upto witness witness ++
  if Nat.eqb (encode_code_trace (decode_code_trace witness)) witness
  then []
  else [emit_false_equation].

Definition emit_trace_start_family
    (_prog : MachineProgram) (input _witness : nat) : equation_family :=
  [emit_linear_const_equation (trace_code_var 0) (start_code input)].

Fixpoint emit_trace_step_family_upto
    (prog : MachineProgram) (witness count : nat) : equation_family :=
  match count with
  | 0 => []
  | S count' =>
      emit_trace_step_family_upto prog witness count' ++
      [emit_linear_const_equation
         (trace_code_var (S count'))
         (StepCode prog (code_trace_nth count' witness))]
  end.

Definition emit_trace_step_family
    (prog : MachineProgram) (_input witness : nat) : equation_family :=
  emit_trace_step_family_upto prog witness (trace_witness_step_count witness).

Definition emit_trace_halt_family
    (_prog : MachineProgram) (_input witness : nat) : equation_family :=
  let last := trace_witness_last_code witness in
  [emit_linear_const_equation trace_halt_var last] ++
  if halted_code_b last then [] else [emit_false_equation].

Definition emit_trace_family
    (prog : MachineProgram) (input witness : nat) : TraceConstraintFamily :=
  emit_trace_shape_family prog input witness ++
  emit_trace_start_family prog input witness ++
  emit_trace_step_family prog input witness ++
  emit_trace_halt_family prog input witness.

(*@inline@[[`emit_trace_shape_family` is the first genuinely concrete fixed-witness block. It does not inspect halting semantics; it simply pins the trace-channel variables to the primitive-recursive list decoder applied to the supplied witness number `W`.]]@*)
(*@inline@[[`emit_trace_family` is the fixed-witness emitter. It receives a concrete witness code `W` and returns the local FM constraints whose common satisfiability should mean exactly `∃ fuel, FMFixedTracePayload(prog,input,W,fuel)`.]]@*)

Lemma emit_linear_const_equation_wf :
  forall var value,
    equation_wf (emit_linear_const_equation var value).
Proof.
  intros var value.
  unfold emit_linear_const_equation, equation_wf.
  split.
  - constructor.
    + simpl.
      apply Nat.lt_succ_diag_r.
    + constructor.
  - constructor.
    + simpl.
      exact I.
    + constructor.
Qed.

Lemma emit_false_equation_wf :
  equation_wf emit_false_equation.
Proof.
  unfold emit_false_equation, equation_wf.
  split.
  - constructor.
    + simpl.
      exact I.
    + constructor.
  - constructor.
Qed.

Lemma emit_trace_shape_family_upto_wf :
  forall witness bound,
    family_wf (emit_trace_shape_family_upto witness bound).
Proof.
  intros witness bound.
  induction bound as [|bound IH]; simpl.
  - apply family_wf_singleton.
    apply emit_linear_const_equation_wf.
  - rewrite family_wf_app.
    split.
    + exact IH.
    + apply family_wf_singleton.
      apply emit_linear_const_equation_wf.
Qed.

Lemma emit_trace_shape_family_wf :
  forall prog input witness,
    family_wf (emit_trace_shape_family prog input witness).
Proof.
  intros prog input witness.
  unfold emit_trace_shape_family.
  rewrite family_wf_app.
  split.
  - apply emit_trace_shape_family_upto_wf.
  - destruct (Nat.eqb (encode_code_trace (decode_code_trace witness)) witness).
    + apply family_wf_nil.
    + apply family_wf_singleton.
      apply emit_false_equation_wf.
Qed.

Lemma emit_trace_start_family_wf :
  forall prog input witness,
    family_wf (emit_trace_start_family prog input witness).
Proof.
  intros prog input witness.
  unfold emit_trace_start_family.
  apply family_wf_singleton.
  apply emit_linear_const_equation_wf.
Qed.

Lemma emit_trace_step_family_upto_wf :
  forall prog witness count,
    family_wf (emit_trace_step_family_upto prog witness count).
Proof.
  intros prog witness count.
  induction count as [|count IH]; simpl.
  - apply family_wf_nil.
  - rewrite family_wf_app.
    split.
    + exact IH.
    + apply family_wf_singleton.
      apply emit_linear_const_equation_wf.
Qed.

Lemma emit_trace_step_family_wf :
  forall prog input witness,
    family_wf (emit_trace_step_family prog input witness).
Proof.
  intros prog input witness.
  unfold emit_trace_step_family.
  apply emit_trace_step_family_upto_wf.
Qed.

Lemma emit_trace_halt_family_wf :
  forall prog input witness,
    family_wf (emit_trace_halt_family prog input witness).
Proof.
  intros prog input witness.
  unfold emit_trace_halt_family.
  rewrite family_wf_app.
  split.
  - apply family_wf_singleton.
    apply emit_linear_const_equation_wf.
  - destruct (halted_code_b (trace_witness_last_code witness)).
    + apply family_wf_nil.
    + apply family_wf_singleton.
      apply emit_false_equation_wf.
Qed.

Theorem emit_trace_family_wf :
  forall prog input witness,
    family_wf (emit_trace_family prog input witness).
Proof.
  intros prog input witness.
  unfold emit_trace_family.
  repeat rewrite family_wf_app.
  repeat split.
  - apply emit_trace_shape_family_wf.
  - apply emit_trace_start_family_wf.
  - apply emit_trace_step_family_wf.
  - apply emit_trace_halt_family_wf.
Qed.

(*@inline@[[`emit_trace_family_wf` is the structural certification theorem for the fixed-witness compiler block. It says the emitted family is not merely satisfiable in the intended cases; every atomic equation it emits is also well-scoped with respect to the arities declared in `P002_00`.]]@*)

Theorem FMValidTrace_iff_exists_fixed_trace_payload :
  forall prog input witness,
    FMValidTrace prog input witness <->
    exists fuel, FMFixedTracePayload prog input witness fuel.
Proof.
  intros prog input witness.
  rewrite FMValidTrace_unfold.
  unfold RawTraceWitness.
  apply RawCodeTraceWitnessFrom_unfold.
Qed.

Theorem FMValidTrace_unfold_full :
  forall prog input witness,
    FMValidTrace prog input witness <->
    exists fuel,
      witness =
        encode_code_trace
          (code_run_trace (StepCode prog) fuel (start_code input)) /\
      halted_state
        (decode_state
           (code_run_last (StepCode prog) fuel (start_code input))).
Proof.
  exact FMValidTrace_iff_exists_fixed_trace_payload.
Qed.

Lemma fixed_trace_payload_fuel_le_witness :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    S fuel <= witness.
Proof.
  intros prog input witness fuel [Hwitness _].
  rewrite Hwitness.
  rewrite <- (code_run_trace_length (StepCode prog) fuel (start_code input)).
  apply encode_nat_list_ge_length.
Qed.

Lemma fixed_trace_payload_decodes_trace :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    decode_code_trace witness =
    code_run_trace (StepCode prog) fuel (start_code input).
Proof.
  intros prog input witness fuel [Hwitness _].
  rewrite Hwitness.
  apply decode_code_trace_encode_code_trace.
Qed.

Lemma fixed_trace_payload_witness_fixed :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_witness_fixed witness.
Proof.
  intros prog input witness fuel [Hwitness _].
  unfold trace_witness_fixed.
  rewrite Hwitness.
  rewrite decode_code_trace_encode_code_trace.
  reflexivity.
Qed.

(*@inline@[[`fixed_trace_payload_fuel_le_witness` is the numeric budget fact needed for the future fixed-witness emitter. Once a witness `W` really encodes a run of fuel `T`, the witness number itself is large enough to bound all time indices `0..T`. This keeps later witness decoding syntax-driven and primitive recursive on `W`.]]@*)
(*@inline@[[`fixed_trace_payload_decodes_trace` is the exact adequacy bridge for fixed-witness compilation: if `W` is a genuine trace witness, then the primitive-recursive decoder on `W` recovers the concrete run trace that the later shape/start/step/halt emitters should mirror.]]@*)

Theorem emit_trace_family_unfold :
  forall prog input witness,
    emit_trace_family prog input witness =
      emit_trace_shape_family prog input witness ++
      emit_trace_start_family prog input witness ++
      emit_trace_step_family prog input witness ++
      emit_trace_halt_family prog input witness.
Proof.
  reflexivity.
Qed.

Lemma emit_linear_const_equation_correct :
  forall rho var value,
    solves (emit_linear_const_equation var value) rho <->
    rho var = value.
Proof.
  intros rho var value.
  unfold solves, emit_linear_const_equation.
  split.
  - intros [[Hlhs Hrhs] Hsol].
    change
      (eval_poly [{| coeff := 1; mono := m_linear var |}] rho =
       eval_poly [{| coeff := value; mono := m_const |}] rho) in Hsol.
    unfold eval_poly, eval_term, eval_monomial in Hsol.
    simpl in Hsol.
    lia.
  - intro Hvalue.
    split.
    + split.
      * constructor.
        -- simpl. apply Nat.lt_succ_diag_r.
        -- constructor.
      * constructor.
        -- simpl. trivial.
        -- constructor.
    + change
        (eval_poly [{| coeff := 1; mono := m_linear var |}] rho =
         eval_poly [{| coeff := value; mono := m_const |}] rho).
      unfold eval_poly, eval_term, eval_monomial.
      simpl.
      lia.
Qed.

Theorem trace_start_family_correct :
  forall prog input witness rho,
    solves_all (emit_trace_start_family prog input witness) rho <->
    trace_channels_start prog input witness rho.
Proof.
  intros prog input witness rho.
  unfold emit_trace_start_family, trace_channels_start, trace_channel_code, trace_code_var.
  rewrite solves_all_singleton.
  rewrite emit_linear_const_equation_correct.
  reflexivity.
Qed.

Lemma emit_trace_shape_family_upto_correct :
  forall witness bound rho,
    solves_all (emit_trace_shape_family_upto witness bound) rho <->
    forall t,
      t <= bound ->
      trace_channel_code rho t = code_trace_nth t witness.
Proof.
  intros witness bound.
  induction bound as [|bound IH]; intro rho.
  - split.
    + intro Hsat.
      simpl in Hsat.
      rewrite solves_all_singleton in Hsat.
      rewrite emit_linear_const_equation_correct in Hsat.
      intros t Ht.
      assert (t = 0) by lia.
      subst t.
      exact Hsat.
    + intro Hshape.
      simpl.
      rewrite solves_all_singleton.
      rewrite emit_linear_const_equation_correct.
      exact (Hshape 0 (Nat.le_refl 0)).
  - simpl.
    rewrite solves_all_app.
    rewrite solves_all_singleton.
    rewrite emit_linear_const_equation_correct.
    rewrite IH.
    split.
    + intros [Hprev Hlast] t Ht.
      destruct (Nat.eq_dec t (S bound)) as [->|Hneq].
      * exact Hlast.
      * apply Hprev.
        lia.
    + intro Hshape.
      split.
      * intros t Ht.
        apply Hshape.
        lia.
      * exact (Hshape (S bound) (Nat.le_refl _)).
Qed.

Lemma emit_false_equation_unsat_shape :
  forall rho,
    ~ solves emit_false_equation rho.
Proof.
  intros rho [Hwf Hsol].
  unfold emit_false_equation in Hsol.
  unfold eval_poly, eval_term, eval_monomial in Hsol.
  simpl in Hsol.
  lia.
Qed.

Theorem trace_shape_family_correct :
  forall prog input witness rho,
    solves_all (emit_trace_shape_family prog input witness) rho <->
    trace_channels_match_witness prog input witness rho /\
    trace_witness_fixed witness.
Proof.
  intros prog input witness rho.
  unfold emit_trace_shape_family, trace_channels_match_witness, trace_witness_fixed.
  set (repair := encode_code_trace (decode_code_trace witness)).
  destruct (Nat.eqb_spec repair witness) as [Hfix|Hfix].
  - rewrite app_nil_r.
    rewrite emit_trace_shape_family_upto_correct.
    split.
    + intro Hshape.
      split.
      * exact Hshape.
      * exact Hfix.
    + intros [Hshape _].
      exact Hshape.
  - rewrite solves_all_app.
    rewrite solves_all_singleton.
    split.
    + intros [_ Hfalse].
      exfalso.
      exact (emit_false_equation_unsat_shape rho Hfalse).
    + intros [_ Hfixed].
      exfalso.
      apply Hfix.
      exact Hfixed.
Qed.

Lemma emit_trace_step_family_upto_correct :
  forall prog witness count rho,
    solves_all (emit_trace_step_family_upto prog witness count) rho <->
    forall t,
      S t <= count ->
      trace_channel_code rho (S t) =
      StepCode prog (code_trace_nth t witness).
Proof.
  intros prog witness count.
  induction count as [|count IH]; intro rho.
  - split.
    + intros _ t Hle.
      lia.
    + intro Hstep.
      apply solves_all_nil.
  - simpl.
    rewrite solves_all_app.
    rewrite solves_all_singleton.
    rewrite emit_linear_const_equation_correct.
    rewrite IH.
    split.
    + intros [Hprev Hlast] t Hle.
      destruct (Nat.eq_dec (S t) (S count)) as [Heq|Hneq].
      * inversion Heq.
        exact Hlast.
      * apply Hprev.
        lia.
    + intro Hstep.
      split.
      * intros t Hle.
        apply Hstep.
        lia.
      * apply Hstep.
        lia.
Qed.

Theorem trace_step_family_correct :
  forall prog input witness rho,
  solves_all (emit_trace_step_family prog input witness) rho <->
    step_channels_follow_witness prog input witness rho.
Proof.
  intros prog input witness rho.
  unfold emit_trace_step_family, step_channels_follow_witness, trace_witness_step_count.
  rewrite emit_trace_step_family_upto_correct.
  split.
  - intros Hstep t Hlt.
    apply Hstep.
    lia.
  - intros Hstep t Hle.
    apply Hstep.
    lia.
Qed.

Lemma emit_false_equation_unsat :
  forall rho,
    ~ solves emit_false_equation rho.
Proof.
  intros rho [Hwf Hsol].
  unfold emit_false_equation in Hsol.
  unfold eval_poly, eval_term, eval_monomial in Hsol.
  simpl in Hsol.
  lia.
Qed.

Theorem trace_halt_family_correct_witness :
  forall prog input witness rho,
    solves_all (emit_trace_halt_family prog input witness) rho <->
    trace_channels_halt_witness prog input witness rho.
Proof.
  intros prog input witness rho.
  unfold emit_trace_halt_family, trace_channels_halt_witness.
  set (last := trace_witness_last_code witness).
  destruct (halted_code_b last) eqn:Hhaltb.
  - rewrite app_nil_r.
    rewrite solves_all_singleton.
    rewrite emit_linear_const_equation_correct.
    split.
    + intro Hlast.
      split.
      * unfold trace_channel_halt_code.
        exact Hlast.
      * unfold trace_channel_halt_code.
        rewrite Hlast.
        apply halted_code_b_correct.
        exact Hhaltb.
    + intros [Hlast _].
      exact Hlast.
  - rewrite solves_all_app.
    rewrite solves_all_singleton.
    rewrite emit_linear_const_equation_correct.
    rewrite solves_all_singleton.
    split.
    + intros [_ Hfalse].
      exfalso.
      exact (emit_false_equation_unsat rho Hfalse).
    + intros [Hlast Hhalt].
      apply halted_code_b_correct in Hhalt.
      rewrite Hlast in Hhalt.
      rewrite Hhaltb in Hhalt.
      discriminate.
Qed.

(* Historical note. The older completeness route went through a stronger
   conjecture `trace_halt_family_correct` whose conclusion packaged an
   existential fuel, a witness/run equality, a final code equality and a
   halting obligation all at once. The current compiler reconstructs the
   equivalent content from the concrete witness-level blocks
   (`trace_channels_match_witness`, `trace_channels_start`,
   `step_channels_follow_witness`, `trace_channels_halt_witness`) via
   `witness_blocks_imply_fixed_payload`, and that stronger conjecture is no
   longer needed. It has been removed to keep the axiom surface honest. *)

Lemma trace_family_valuation_halt_code :
  forall prog input witness fuel,
    trace_channel_halt_code (trace_family_valuation prog input witness fuel) =
    code_run_last (StepCode prog) fuel (start_code input).
Proof.
  reflexivity.
Qed.

Lemma trace_family_valuation_code_channel :
  forall prog input witness fuel t,
    trace_channel_code (trace_family_valuation prog input witness fuel) t =
    if Nat.leb t fuel
    then code_run_last (StepCode prog) t (start_code input)
    else 0.
Proof.
  reflexivity.
Qed.

Lemma trace_family_valuation_code_channel_bounded :
  forall prog input witness fuel t,
    t <= fuel ->
    trace_channel_code (trace_family_valuation prog input witness fuel) t =
    code_run_last (StepCode prog) t (start_code input).
Proof.
  intros prog input witness fuel t Hle.
  rewrite trace_family_valuation_code_channel.
  destruct (Nat.leb_spec0 t fuel) as [Htf|Htf].
  - reflexivity.
  - lia.
Qed.

Lemma trace_family_valuation_models_start :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_channels_start
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel _.
  unfold trace_channels_start.
  rewrite trace_family_valuation_code_channel_bounded by lia.
  reflexivity.
Qed.

Lemma code_run_last_next_comm :
  forall next fuel start,
    code_run_last next fuel (next start) =
    next (code_run_last next fuel start).
Proof.
  intros next fuel.
  induction fuel as [|fuel IH]; intros start.
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma code_run_last_succ :
  forall next fuel start,
    code_run_last next (S fuel) start =
    next (code_run_last next fuel start).
Proof.
  intros next fuel start.
  simpl.
  apply code_run_last_next_comm.
Qed.

Lemma trace_family_valuation_models_step :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    step_channels_follow_StepCode
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel [Hwitness _].
  exists fuel.
  split.
  - exact Hwitness.
  - intros t Hlt.
    rewrite trace_family_valuation_code_channel_bounded by lia.
    rewrite trace_family_valuation_code_channel_bounded by lia.
    apply code_run_last_succ.
Qed.

Lemma fixed_trace_payload_witness_length :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_witness_length witness = S fuel.
Proof.
  intros prog input witness fuel Hpayload.
  unfold trace_witness_length.
  rewrite (fixed_trace_payload_decodes_trace prog input witness fuel) by exact Hpayload.
  apply (code_run_trace_length (StepCode prog) fuel (start_code input)).
Qed.

Lemma trace_family_valuation_models_step_witness :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    step_channels_follow_witness
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel Hpayload t Hlt.
  destruct Hpayload as [Hwitness Hhalt].
  assert (Hlen : trace_witness_length witness = S fuel).
  {
    apply (fixed_trace_payload_witness_length prog input witness fuel).
    split; assumption.
  }
  rewrite trace_family_valuation_code_channel_bounded by lia.
  rewrite Hwitness.
  rewrite code_trace_nth_encode_code_trace.
  rewrite code_run_last_succ.
  f_equal.
  symmetry.
  apply code_run_trace_nth.
  lia.
Qed.

Lemma trace_family_valuation_models_halt :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_channels_halt
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel [Hwitness Hhalt].
  exists fuel.
  split.
  - exact Hwitness.
  - split.
    + apply trace_family_valuation_halt_code.
    + rewrite trace_family_valuation_halt_code.
      exact Hhalt.
Qed.

Lemma trace_family_valuation_models_halt_witness :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_channels_halt_witness
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel Hpayload.
  destruct Hpayload as [Hwitness Hhalt].
  split.
  - unfold trace_witness_last_code, trace_witness_step_count.
    rewrite trace_family_valuation_halt_code.
    rewrite (fixed_trace_payload_witness_length prog input witness fuel)
      by (split; assumption).
    simpl.
    rewrite Hwitness.
    rewrite code_trace_nth_encode_code_trace.
    symmetry.
    apply code_run_trace_nth.
    lia.
  - rewrite trace_family_valuation_halt_code.
    exact Hhalt.
Qed.

Lemma trace_family_valuation_models_match_run :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_channels_match_run
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel [Hwitness _].
  exists fuel.
  split.
  - exact Hwitness.
  - intros t Hle.
    rewrite trace_family_valuation_code_channel_bounded by exact Hle.
    rewrite Hwitness.
    rewrite code_trace_nth_encode_code_trace.
    symmetry.
    apply code_run_trace_nth.
    exact Hle.
Qed.

Lemma trace_family_valuation_models_match_witness :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_channels_match_witness
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel Hpayload t Hle_witness.
  destruct Hpayload as [Hwitness Hhalt].
  destruct (Nat.leb_spec0 t fuel) as [Hle_fuel|Hgt_fuel].
  - rewrite trace_family_valuation_code_channel_bounded by exact Hle_fuel.
    rewrite Hwitness.
    rewrite code_trace_nth_encode_code_trace.
    symmetry.
    apply code_run_trace_nth.
    exact Hle_fuel.
  - rewrite trace_family_valuation_code_channel.
    destruct (Nat.leb_spec0 t fuel) as [Hle_again|Hgt_again].
    + lia.
    + rewrite Hwitness.
      rewrite code_trace_nth_encode_code_trace.
      symmetry.
      apply nth_overflow.
      rewrite code_run_trace_length.
      lia.
Qed.

Lemma start_code_nonzero :
  forall input,
    start_code input <> 0.
Proof.
  intros input H0.
  pose proof (initial_state_components input) as [Hip0 [Hr10 Hr20]].
  assert (Hip1 : ip_code 1 = 1).
  {
    unfold ip_code, band_code, band_support, IP_offset.
    rewrite (map_ext (fun i => 0 + i) (fun i => i)) by (intro; reflexivity).
    rewrite map_id.
    apply Z0_sound.
  }
  unfold start_code in H0.
  rewrite encode_state_as_components in H0.
  rewrite Hip0, Hr10, Hr20 in H0.
  rewrite Hip1 in H0.
  lia.
Qed.

Lemma nat_list_eq_by_nth :
  forall (xs ys : list nat),
    length xs = length ys ->
    (forall i, i < length xs -> nth i xs 0 = nth i ys 0) ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] Hlen Hnth; simpl in *.
  - reflexivity.
  - discriminate.
  - discriminate.
  - f_equal.
    + specialize (Hnth 0 ltac:(lia)).
      simpl in Hnth.
      exact Hnth.
    + apply IH.
      * lia.
      * intros i Hi.
        specialize (Hnth (S i)).
        assert (S i < S (length xs)) by lia.
        specialize (Hnth H).
        simpl in Hnth.
        exact Hnth.
Qed.

Lemma witness_blocks_imply_fixed_payload :
  forall prog input witness rho,
    trace_channels_match_witness prog input witness rho ->
    trace_witness_fixed witness ->
    trace_channels_start prog input witness rho ->
    step_channels_follow_witness prog input witness rho ->
    trace_channels_halt_witness prog input witness rho ->
    exists fuel, FMFixedTracePayload prog input witness fuel.
Proof.
  intros prog input witness rho Hmatch Hfixed Hstart Hstep Hhalt.
  set (fuel := trace_witness_step_count witness).
  assert (Hstart_code : code_trace_nth 0 witness = start_code input).
  {
    rewrite <- Hstart.
    symmetry.
    apply Hmatch.
    lia.
  }
  assert (Hwitness_nz : witness <> 0).
  {
    intro Hw0.
    subst witness.
    simpl in Hstart_code.
    apply (start_code_nonzero input).
    symmetry.
    exact Hstart_code.
  }
  assert (Hlen_pos : 0 < trace_witness_length witness).
  {
    apply decode_code_trace_positive.
    exact Hwitness_nz.
  }
  assert (Hlen_fuel : trace_witness_length witness = S fuel).
  {
    unfold fuel, trace_witness_step_count.
    lia.
  }
  assert (Hrun_nth :
    forall t,
      t <= fuel ->
      code_trace_nth t witness =
      code_run_last (StepCode prog) t (start_code input)).
  {
    intros t Hle.
    induction t as [|t IH].
    - exact Hstart_code.
    - assert (Hstep_lt : S t < trace_witness_length witness).
      {
        rewrite Hlen_fuel.
        lia.
      }
      specialize (Hstep t Hstep_lt).
      assert (Hmatch_t :
        trace_channel_code rho (S t) = code_trace_nth (S t) witness).
      {
        apply Hmatch.
        eapply Nat.le_trans with (m := trace_witness_length witness).
        - rewrite Hlen_fuel. lia.
        - apply decode_code_trace_length_le.
      }
      rewrite Hmatch_t in Hstep.
      rewrite IH in Hstep by lia.
      rewrite Hstep.
      rewrite code_run_last_succ.
      reflexivity.
  }
  assert (Htrace_eq :
    decode_code_trace witness =
    code_run_trace (StepCode prog) fuel (start_code input)).
  {
    apply nat_list_eq_by_nth.
    - rewrite code_run_trace_length.
      exact Hlen_fuel.
    - intros i Hi.
      change (length (decode_code_trace witness))
        with (trace_witness_length witness) in Hi.
      rewrite Hlen_fuel in Hi.
      rewrite nth_decode_code_trace
        by (change (length (decode_code_trace witness))
              with (trace_witness_length witness);
            rewrite Hlen_fuel; lia).
      rewrite code_run_trace_nth by lia.
      apply Hrun_nth.
      lia.
  }
  exists fuel.
  split.
  - rewrite <- Hfixed.
    rewrite Htrace_eq.
    reflexivity.
  - destruct Hhalt as [Hhalt_code Hhalted].
    rewrite Hhalt_code in Hhalted.
    unfold trace_witness_last_code, fuel, trace_witness_step_count in Hhalted.
    rewrite Hrun_nth in Hhalted.
    + exact Hhalted.
    + lia.
Qed.

Lemma emit_trace_family_sound :
  forall prog input witness,
    FMValidTrace prog input witness ->
    family_satisfiable (emit_trace_family prog input witness).
Proof.
  intros prog input witness.
  rewrite FMValidTrace_unfold_full.
  intros [fuel Hpayload].
  set (rho := trace_family_valuation prog input witness fuel).
  apply (proj2 (family_satisfiable_iff (emit_trace_family prog input witness))).
  exists rho.
  rewrite emit_trace_family_unfold.
  repeat rewrite solves_all_app.
  repeat split.
  - apply (proj2 (trace_shape_family_correct prog input witness rho)).
    split.
    + apply trace_family_valuation_models_match_witness.
      exact Hpayload.
    + apply fixed_trace_payload_witness_fixed with (prog := prog) (input := input) (fuel := fuel).
      exact Hpayload.
  - apply (proj2 (trace_start_family_correct prog input witness rho)).
    apply trace_family_valuation_models_start.
    exact Hpayload.
  - apply (proj2 (trace_step_family_correct prog input witness rho)).
    apply trace_family_valuation_models_step_witness.
    exact Hpayload.
  - apply (proj2 (trace_halt_family_correct_witness prog input witness rho)).
    apply trace_family_valuation_models_halt_witness.
    exact Hpayload.
Qed.

Lemma emit_trace_family_complete :
  forall prog input witness,
    family_satisfiable (emit_trace_family prog input witness) ->
    FMValidTrace prog input witness.
Proof.
  intros prog input witness Hsat.
  apply (proj1 (family_satisfiable_iff (emit_trace_family prog input witness))) in Hsat.
  destruct Hsat as [rho Hsat].
  (* Completeness now runs entirely through the concrete fixed-witness blocks:
     recover shape/start/step/halt facts from one satisfying valuation, then
     reconstruct one `FMFixedTracePayload`. *)
  rewrite emit_trace_family_unfold in Hsat.
  repeat rewrite solves_all_app in Hsat.
  destruct Hsat as [Hshape [Hstart [Hstep Hhalt]]].
  apply (proj1 (trace_shape_family_correct prog input witness rho)) in Hshape.
  apply (proj1 (trace_start_family_correct prog input witness rho)) in Hstart.
  apply (proj1 (trace_step_family_correct prog input witness rho)) in Hstep.
  apply (proj1 (trace_halt_family_correct_witness prog input witness rho)) in Hhalt.
  rewrite FMValidTrace_unfold_full.
  destruct Hshape as [Hmatch Hfixed].
  destruct (witness_blocks_imply_fixed_payload
              prog input witness rho Hmatch Hfixed Hstart Hstep Hhalt)
    as [fuel Hpayload].
  exists fuel.
  exact Hpayload.
Qed.

Theorem trace_family_correct :
  forall prog input witness,
    FMValidTrace prog input witness <->
    family_satisfiable (emit_trace_family prog input witness).
Proof.
  intros prog input witness.
  split.
  - apply emit_trace_family_sound.
  - apply emit_trace_family_complete.
Qed.
