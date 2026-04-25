(*P002_04__Trace_Family_Emitter.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / P002_04__Trace_Family_Emitter                   │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer emits a finite cubic family for one concrete FM trace witness.

  Its main theorem is `trace_family_correct`: the emitted family is
  satisfiable exactly when the supplied raw witness satisfies `FMValidTrace`.
  The construction is effective; it uses primitive-recursive decoding and
  boolean checks, with no search policy or classical choice in this file.

*)

(*
│
│          This emitter layer consumes the encoded-trace and shared
│          family semantics from `P002_03__Witness_Family_Core`.
│
*)

(*                              P002₀₃ → P002₀₄                               *)

From P002 Require Export P002_03__Witness_Family_Core.


(*
│
│          A trace constraint family is the local family type from the
│          witness/family core.
│
*)

(*                   TraceConstraintFamily ≔ EquationFamily                   *)

Definition TraceConstraintFamily : Type := equation_family.

(*
│
│          The fixed trace payload from an explicit start code says
│          that `witness` is exactly the encoded concrete run of
│          length `fuel`, and that the final code is halted.
│
*)

(*                     FixedPayloadFrom(prog,start,W,T) ⇔                     *)
(*              W=EncodeTrace(CodeRunTrace(StepCode,T,start)) ∧               *)
(*          HaltedState(DecodeState(CodeRunLast(StepCode,T,start)))           *)

Definition FMFixedTracePayloadFrom
    (prog : MachineProgram) (start witness fuel : nat) : Prop :=
  witness =
    encode_code_trace
      (code_run_trace (StepCode prog) fuel start) /\
  halted_state
    (decode_state (code_run_last (StepCode prog) fuel start)).

(*
│
│          The input-specialized fixed trace payload starts from the
│          encoded initial state of the input.
│
*)

(* FixedPayload(prog,input,W,T) ⇔ FixedPayloadFrom(prog,StartCode(input),W,T) *)

Definition FMFixedTracePayload
    (prog : MachineProgram) (input witness fuel : nat) : Prop :=
  FMFixedTracePayloadFrom prog (start_code input) witness fuel.

(*
│
│          The canonical valuation for a real run stores the final
│          halted code in variable `0` and the time-`t` run code in
│          variable `S t`, defaulting out-of-range channels to zero.
│
*)

(*ρ(0)=CodeRunLast(StepCode,T,start); ρ(S t)=CodeRunLast(StepCode,t,start) for*)
(*                                    t≤T                                     *)

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

(*
│
│          Variable `0` is reserved for the final halt-code channel.
│
*)

(*                                 HaltVar=0                                  *)

Definition trace_halt_var : nat := 0.

(*
│
│          The code channel for time `t` is variable `S t`.
│
*)

(*                               CodeVar(t)=t+1                               *)

Definition trace_code_var (t : nat) : nat := S t.

(*
│
│          Reading the time-`t` code channel means evaluating the
│          valuation at `CodeVar(t)`.
│
*)

(*                       CodeChannel(ρ,t)=ρ(CodeVar(t))                       *)

Definition trace_channel_code (rho : valuation) (t : nat) : nat :=
  rho (trace_code_var t).

(*
│
│          Reading the halt channel means evaluating the valuation at
│          `HaltVar`.
│
*)

(*                         HaltChannel(ρ)=ρ(HaltVar)                          *)

Definition trace_channel_halt_code (rho : valuation) : nat :=
  rho trace_halt_var.

(*
│
│          The witness length is the length of the decoded trace.
│
*)

(*                  WitnessLength(W)=length(DecodeTrace(W))                   *)

Definition trace_witness_length (witness : nat) : nat :=
  length (decode_code_trace witness).

(*
│
│          The step count is one less than the decoded witness length,
│          using predecessor so empty traces yield zero.
│
*)

(*                    StepCount(W)=pred(WitnessLength(W))                     *)

Definition trace_witness_step_count (witness : nat) : nat :=
  Nat.pred (trace_witness_length witness).

(*
│
│          The last witness code is the decoded trace code at the
│          computed step count.
│
*)

(*                WitnessLastCode(W)=TraceNth(StepCount(W),W)                 *)

Definition trace_witness_last_code (witness : nat) : nat :=
  code_trace_nth (trace_witness_step_count witness) witness.

(*
│
│          The witness-matching predicate says every bounded code
│          channel agrees with numeric indexing into the witness.
│
*)

(*             t ≤ StepCount(W) ⇒ CodeChannel(ρ,t)=TraceNth(t,W)              *)

Definition trace_channels_match_witness
    (_prog : MachineProgram) (_input witness : nat) (rho : valuation) : Prop :=
  forall t,
    t <= trace_witness_step_count witness ->
    trace_channel_code rho t = code_trace_nth t witness.

(*
│
│          The start-channel predicate says time zero stores the
│          input-derived start code.
│
*)

(*                     CodeChannel(ρ,0)=StartCode(input)                      *)

Definition trace_channels_start
    (_prog : MachineProgram) (input witness : nat) (rho : valuation) : Prop :=
  trace_channel_code rho 0 = start_code input.

(*
│
│          The step-channel predicate says every successor code
│          channel agrees with applying `StepCode` to the previous
│          witness code.
│
*)

(*  S t < WitnessLength(W) ⇒ CodeChannel(ρ,S t)=StepCode(prog,TraceNth(t,W))  *)

Definition step_channels_follow_witness
    (prog : MachineProgram) (_input witness : nat) (rho : valuation) : Prop :=
  forall t,
    S t < trace_witness_length witness ->
    trace_channel_code rho (S t) =
    StepCode prog (code_trace_nth t witness).

(*
│
│          A witness is fixed when decoding and re-encoding it returns
│          the same number.
│
*)

(*            TraceWitnessFixed(W) ⇔ EncodeTrace(DecodeTrace(W))=W            *)

Definition trace_witness_fixed (witness : nat) : Prop :=
  encode_code_trace (decode_code_trace witness) = witness.

(*
│
│          The halt-channel predicate says the halt channel stores the
│          last witness code and that this decoded code is halted.
│
*)

(*HaltChannel(ρ)=WitnessLastCode(W) ∧ HaltedState(DecodeState(HaltChannel(ρ)))*)

Definition trace_channels_halt_witness
    (_prog : MachineProgram) (_input witness : nat) (rho : valuation) : Prop :=
  trace_channel_halt_code rho = trace_witness_last_code witness /\
  halted_state (decode_state (trace_channel_halt_code rho)).

(*
│
│          The linear-constant equation pins one variable to one
│          natural constant.
│
*)

(*                    LinearConst(var,value) : xᵥₐᵣ=value                     *)

Definition emit_linear_const_equation (var value : nat) : h10_nd3n_equation :=
  {|
    var_count := S var;
    lhs_terms := [{| coeff := 1; mono := m_linear var |}];
    rhs_terms := [{| coeff := value; mono := m_const |}]
  |}.

(*
│
│          The false equation is the unsatisfiable constant equation
│          `1=0`.
│
*)

(*                               FalseEq : 1=0                                *)

Definition emit_false_equation : h10_nd3n_equation :=
  {|
    var_count := 0;
    lhs_terms := [{| coeff := 1; mono := m_const |}];
    rhs_terms := []
  |}.

(*
│
│          The bounded shape emitter pins every code channel from `0`
│          through `bound` to the corresponding indexed value of the
│          supplied witness.
│
*)

(*            ShapeUpTo(W,bound)=⋀ₜ≤bound CodeVar(t)=TraceNth(t,W)            *)

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

(*
│
│          The shape family pins all witness code channels and adds
│          `FalseEq` if the witness does not decode and re-encode to
│          itself.
│
*)

(*      ShapeFamily(W)=ShapeUpTo(W,StepCount(W)) ∧ TraceWitnessFixed(W)       *)

Definition emit_trace_shape_family
    (_prog : MachineProgram) (_input witness : nat) : equation_family :=
  emit_trace_shape_family_upto witness (trace_witness_step_count witness) ++
  if Nat.eqb (encode_code_trace (decode_code_trace witness)) witness
  then []
  else [emit_false_equation].

(*
│
│          The start family pins the time-zero code channel to the
│          input-derived start code.
│
*)

(*              StartFamily(input) : CodeVar(0)=StartCode(input)              *)

Definition emit_trace_start_family
    (_prog : MachineProgram) (input _witness : nat) : equation_family :=
  [emit_linear_const_equation (trace_code_var 0) (start_code input)].

(*
│
│          The step family up to `count` pins each successor channel
│          to the executable next-state image of the previous witness
│          code.
│
*)

(* StepUpTo(prog,W,count)=⋀ₜ<count CodeVar(t+1)=StepCode(prog,TraceNth(t,W))  *)

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

(*
│
│          The step family emits all step equations determined by the
│          witness step count.
│
*)

(*              StepFamily(prog,W)=StepUpTo(prog,W,StepCount(W))              *)

Definition emit_trace_step_family
    (prog : MachineProgram) (_input witness : nat) : equation_family :=
  emit_trace_step_family_upto prog witness (trace_witness_step_count witness).

(*
│
│          The halt family pins the halt channel to the last witness
│          code and adds `FalseEq` if that code is not halted.
│
*)

(*HaltFamily(W) : HaltVar=WitnessLastCode(W) ∧ HaltedCodeB(WitnessLastCode(W))*)

Definition emit_trace_halt_family
    (_prog : MachineProgram) (_input witness : nat) : equation_family :=
  let last := trace_witness_last_code witness in
  [emit_linear_const_equation trace_halt_var last] ++
  if halted_code_b last then [] else [emit_false_equation].

(*
│
│          The full fixed-witness family concatenates the shape,
│          start, step, and halt blocks.
│
*)

(*     TraceFamily(prog,input,W)=ShapeFamily(W) ++ StartFamily(input) ++      *)
(*                    StepFamily(prog,W) ++ HaltFamily(W)                     *)

Definition emit_trace_family
    (prog : MachineProgram) (input witness : nat) : TraceConstraintFamily :=
  emit_trace_shape_family prog input witness ++
  emit_trace_start_family prog input witness ++
  emit_trace_step_family prog input witness ++
  emit_trace_halt_family prog input witness.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                     FIXED-WITNESS EMITTER CONTRACTS                     ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The well-formedness contract says the emitter always
│          produces a well-formed family.
│
*)

(*       EmitterWF(emit) ⇔ ∀ prog input W. FamilyWF(emit(prog,input,W))       *)

Definition fixed_trace_family_emitter_wf
    (emit_trace : MachineProgram -> nat -> nat -> TraceConstraintFamily) : Prop :=
  forall prog input witness,
    family_wf (emit_trace prog input witness).

(*
│
│          The payload-correctness contract says the emitted family is
│          satisfiable exactly when some fixed fuel realizes the trace
│          payload.
│
*)

(*        PayloadCorrect(emit) ⇔ (∃ T. FixedPayload(prog,input,W,T)) ⇔        *)
(*                       FamilySat(emit(prog,input,W))                        *)

Definition fixed_trace_family_emitter_payload_correct
    (emit_trace : MachineProgram -> nat -> nat -> TraceConstraintFamily) : Prop :=
  forall prog input witness,
    (exists fuel, FMFixedTracePayload prog input witness fuel) <->
    family_satisfiable (emit_trace prog input witness).

(*
│
│          The correctness contract says the emitted family is
│          satisfiable exactly when the public FM trace predicate
│          holds.
│
*)

(*            EmitterCorrect(emit) ⇔ FMValidTrace(prog,input,W) ⇔             *)
(*                       FamilySat(emit(prog,input,W))                        *)

Definition fixed_trace_family_emitter_correct
    (emit_trace : MachineProgram -> nat -> nat -> TraceConstraintFamily) : Prop :=
  forall prog input witness,
    FMValidTrace prog input witness <->
    family_satisfiable (emit_trace prog input witness).

(*
│
│          The combined contract packages well-formedness and public
│          correctness for every fixed witness.
│
*)

(*            EmitterWithWF(emit) ⇔ FamilyWF(emit(prog,input,W)) ∧            *)
(*        (FMValidTrace(prog,input,W) ⇔ FamilySat(emit(prog,input,W)))        *)

Definition fixed_trace_family_emitter_with_wf
    (emit_trace : MachineProgram -> nat -> nat -> TraceConstraintFamily) : Prop :=
  forall prog input witness,
    family_wf (emit_trace prog input witness) /\
    (FMValidTrace prog input witness <->
     family_satisfiable (emit_trace prog input witness)).

(*
│
│          A linear-constant equation is well-scoped by its single
│          variable.
│
*)

(*                         WF(LinearConst(var,value))                         *)

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

(*
│
│          The false equation is well-formed even though it is
│          unsatisfiable.
│
*)

(*                                WF(FalseEq)                                 *)

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

(*
│
│          Every bounded shape family is well-formed.
│
*)

(*                        FamilyWF(ShapeUpTo(W,bound))                        *)

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

(*
│
│          Every shape family is well-formed, including the optional
│          false equation.
│
*)

(*                          FamilyWF(ShapeFamily(W))                          *)

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

(*
│
│          Every start family is well-formed.
│
*)

(*                        FamilyWF(StartFamily(input))                        *)

Lemma emit_trace_start_family_wf :
  forall prog input witness,
    family_wf (emit_trace_start_family prog input witness).
Proof.
  intros prog input witness.
  unfold emit_trace_start_family.
  apply family_wf_singleton.
  apply emit_linear_const_equation_wf.
Qed.

(*
│
│          Every bounded step family is well-formed.
│
*)

(*                      FamilyWF(StepUpTo(prog,W,count))                      *)

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

(*
│
│          Every step family is well-formed.
│
*)

(*                        FamilyWF(StepFamily(prog,W))                        *)

Lemma emit_trace_step_family_wf :
  forall prog input witness,
    family_wf (emit_trace_step_family prog input witness).
Proof.
  intros prog input witness.
  unfold emit_trace_step_family.
  apply emit_trace_step_family_upto_wf.
Qed.

(*
│
│          Every halt family is well-formed, including the optional
│          false equation.
│
*)

(*                          FamilyWF(HaltFamily(W))                           *)

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

(*
│
│          The full fixed-witness trace family is well-formed.
│
*)

(*                    FamilyWF(TraceFamily(prog,input,W))                     *)

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

(*
│
│          The public FM trace predicate is equivalent to the
│          existence of one fixed trace payload fuel.
│
*)

(*       FMValidTrace(prog,input,W) ⇔ ∃ T. FixedPayload(prog,input,W,T)       *)

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

(*
│
│          The public FM trace predicate unfolds to the concrete
│          encoded run and final halted-code condition.
│
*)

(*                     FMValidTrace(prog,input,W) ⇔ ∃ T.                      *)
(*         W=EncodeTrace(CodeRunTrace(StepCode,T,StartCode(input))) ∧         *)
(*     HaltedState(DecodeState(CodeRunLast(StepCode,T,StartCode(input))))     *)

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

(*
│
│          A fixed payload witness is large enough to cover all
│          `fuel+1` concrete run states.
│
*)

(*                   FixedPayload(prog,input,W,T) ⇒ T+1 ≤ W                   *)

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

(*
│
│          Decoding a fixed payload witness recovers its concrete run
│          trace.
│
*)

(*                       FixedPayload(prog,input,W,T) ⇒                       *)
(*          DecodeTrace(W)=CodeRunTrace(StepCode,T,StartCode(input))          *)

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

(*
│
│          A fixed payload witness is stable under decode/re-encode.
│
*)

(*            FixedPayload(prog,input,W,T) ⇒ TraceWitnessFixed(W)             *)

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

(*
│
│          The full emitter unfolds definitionally to shape, start,
│          step, and halt blocks.
│
*)

(*     TraceFamily=ShapeFamily ++ StartFamily ++ StepFamily ++ HaltFamily     *)

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

(*
│
│          A valuation solves a linear-constant equation exactly when
│          the selected variable has the selected value.
│
*)

(*              Solves(LinearConst(var,value),ρ) ⇔ ρ(var)=value               *)

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

(*
│
│          Solving the start family is equivalent to satisfying the
│          start-channel predicate.
│
*)

(*    SolvesAll(StartFamily(input),ρ) ⇔ CodeChannel(ρ,0)=StartCode(input)     *)

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

(*
│
│          Solving the bounded shape family is equivalent to all
│          bounded code channels matching the witness.
│
*)

(*SolvesAll(ShapeUpTo(W,bound),ρ) ⇔ ∀ t≤bound. CodeChannel(ρ,t)=TraceNth(t,W) *)

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

(*
│
│          The false equation has no solving valuation.
│
*)

(*                            ¬ Solves(FalseEq,ρ)                             *)

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

(*
│
│          Solving the shape family is equivalent to witness-channel
│          matching plus decode/re-encode fixedness.
│
*)

(*   SolvesAll(ShapeFamily(W),ρ) ⇔ MatchWitness(W,ρ) ∧ TraceWitnessFixed(W)   *)

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

(*
│
│          Solving the bounded step family is equivalent to every
│          emitted successor channel matching `StepCode` on the
│          previous witness code.
│
*)

(*     SolvesAll(StepUpTo(prog,W,count),ρ) ⇔ ∀ S t≤count. CodeChannel(ρ,S     *)
(*                      t)=StepCode(prog,TraceNth(t,W))                       *)

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

(*
│
│          Solving the step family is equivalent to the
│          witness-indexed step-channel predicate.
│
*)

(*   SolvesAll(StepFamily(prog,W),ρ) ⇔ StepChannelsFollowWitness(prog,W,ρ)    *)

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

(*
│
│          The false equation is unsatisfiable; this duplicate name is
│          kept for the halt-family proof block.
│
*)

(*                            ¬ Solves(FalseEq,ρ)                             *)

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

(*
│
│          Solving the halt family is equivalent to the halt channel
│          storing the last witness code and that code being halted.
│
*)

(*      SolvesAll(HaltFamily(W),ρ) ⇔ HaltChannel(ρ)=WitnessLastCode(W) ∧      *)
(*                  HaltedState(DecodeState(HaltChannel(ρ)))                  *)

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

(*
│
│          The canonical run valuation reads the concrete final run
│          code from the halt channel.
│
*)

(*         HaltChannel(ρrun)=CodeRunLast(StepCode,T,StartCode(input))         *)

Lemma trace_family_valuation_halt_code :
  forall prog input witness fuel,
    trace_channel_halt_code (trace_family_valuation prog input witness fuel) =
    code_run_last (StepCode prog) fuel (start_code input).
Proof.
  reflexivity.
Qed.

(*
│
│          The canonical run valuation reads the concrete time-`t` run
│          code from code channel `t` when `t≤fuel`, and zero
│          otherwise.
│
*)

(*    CodeChannel(ρrun,t)=if t≤T then CodeRunLast(StepCode,t,start) else 0    *)

Lemma trace_family_valuation_code_channel :
  forall prog input witness fuel t,
    trace_channel_code (trace_family_valuation prog input witness fuel) t =
    if Nat.leb t fuel
    then code_run_last (StepCode prog) t (start_code input)
    else 0.
Proof.
  reflexivity.
Qed.

(*
│
│          Within fuel, the canonical run valuation's code channel is
│          the concrete time-`t` run code.
│
*)

(*          t≤T ⇒ CodeChannel(ρrun,t)=CodeRunLast(StepCode,t,start)           *)

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

(*
│
│          The canonical run valuation satisfies the start-channel
│          predicate.
│
*)

(*                        FixedPayload ⇒ Starts(ρrun)                         *)

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

(*
│
│          Running `fuel` more steps after one step commutes with
│          applying the next function after `fuel` steps.
│
*)

(*      CodeRunLast(next,T,next(start))=next(CodeRunLast(next,T,start))       *)

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

(*
│
│          The `S fuel` last-code iterate is one next-step after the
│          `fuel` iterate.
│
*)

(*        CodeRunLast(next,T+1,start)=next(CodeRunLast(next,T,start))         *)

Lemma code_run_last_succ :
  forall next fuel start,
    code_run_last next (S fuel) start =
    next (code_run_last next fuel start).
Proof.
  intros next fuel start.
  simpl.
  apply code_run_last_next_comm.
Qed.

(*
│
│          A fixed payload witness decodes to a trace of length
│          `fuel+1`.
│
*)

(*            FixedPayload(prog,input,W,T) ⇒ WitnessLength(W)=T+1             *)

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

(*
│
│          The canonical run valuation satisfies the witness-indexed
│          step-channel predicate.
│
*)

(*           FixedPayload ⇒ StepChannelsFollowWitness(prog,W,ρrun)            *)

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

(*
│
│          The canonical run valuation satisfies the halt-channel
│          predicate.
│
*)

(*                     FixedPayload ⇒ HaltWitness(W,ρrun)                     *)

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

(*
│
│          The canonical run valuation satisfies the witness-matching
│          predicate.
│
*)

(*                    FixedPayload ⇒ MatchWitness(W,ρrun)                     *)

Lemma trace_family_valuation_models_match_witness :
  forall prog input witness fuel,
    FMFixedTracePayload prog input witness fuel ->
    trace_channels_match_witness
      prog input witness
      (trace_family_valuation prog input witness fuel).
Proof.
  intros prog input witness fuel Hpayload t Hle_witness.
  destruct Hpayload as [Hwitness Hhalt].
  assert (Hlen : trace_witness_length witness = S fuel).
  {
    apply (fixed_trace_payload_witness_length prog input witness fuel).
    split; assumption.
  }
  assert (Hle_fuel : t <= fuel).
  {
    unfold trace_witness_step_count in Hle_witness.
    rewrite Hlen in Hle_witness.
    lia.
  }
  rewrite trace_family_valuation_code_channel_bounded by exact Hle_fuel.
  rewrite Hwitness.
  rewrite code_trace_nth_encode_code_trace.
  symmetry.
  apply code_run_trace_nth.
  exact Hle_fuel.
Qed.

(*
│
│          Soundness: a valid FM trace witness yields a satisfying
│          valuation for the emitted trace family.
│
*)

(*     FMValidTrace(prog,input,W) ⇒ FamilySat(TraceFamily(prog,input,W))      *)

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

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                               COMPLETENESS                              ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The encoded initial state is nonzero. This prevents a
│          satisfying stream from representing an empty decoded
│          witness.
│
*)

(*                            StartCode(input) ≠ 0                            *)

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

(*
│
│          Two natural lists are equal when they have the same length
│          and the same defaulted nth value at every in-bounds index.
│
*)

(* length(xs)=length(ys) ∧ (∀ i<length(xs). nth(i,xs,0)=nth(i,ys,0)) ⇒ xs=ys  *)

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

(*
│
│          A trace-code stream is a function from time indices to
│          encoded state codes.
│
*)

(*                          TraceCodeStream ≔ ℕ → ℕ                           *)

Definition TraceCodeStream : Type := nat -> nat.

(*
│
│          A stream matches a witness when it agrees with every
│          bounded numeric trace index.
│
*)

(*                  t≤StepCount(W) ⇒ stream(t)=TraceNth(t,W)                  *)

Definition trace_stream_matches_witness
    (stream : TraceCodeStream) (witness : nat) : Prop :=
  forall t,
    t <= trace_witness_step_count witness ->
    stream t = code_trace_nth t witness.

(*
│
│          A stream starts correctly when its time-zero code is the
│          input start code.
│
*)

(*                         stream(0)=StartCode(input)                         *)

Definition trace_stream_starts
    (input : nat) (stream : TraceCodeStream) : Prop :=
  stream 0 = start_code input.

(*
│
│          A stream steps correctly when each successor stream value
│          is `StepCode` applied to the previous witness code.
│
*)

(*     S t < WitnessLength(W) ⇒ stream(S t)=StepCode(prog,TraceNth(t,W))      *)

Definition trace_stream_steps
    (prog : MachineProgram) (witness : nat) (stream : TraceCodeStream) : Prop :=
  forall t,
    S t < trace_witness_length witness ->
    stream (S t) = StepCode prog (code_trace_nth t witness).

(*
│
│          A stream halt certificate pins a halt code to the last
│          witness code and requires that decoded code to be halted.
│
*)

(*          halt=WitnessLastCode(W) ∧ HaltedState(DecodeState(halt))          *)

Definition trace_stream_halt
    (witness halt_code : nat) : Prop :=
  halt_code = trace_witness_last_code witness /\
  halted_state (decode_state halt_code).

(*
│
│          The stream abstraction reconstructs a fixed payload from
│          matching, fixedness, start, step, and halt blocks.
│
*)

(*MatchStream ∧ TraceWitnessFixed ∧ StartStream ∧ StepStream ∧ HaltStream ⇒ ∃ *)
(*                      T. FixedPayload(prog,input,W,T)                       *)

Lemma trace_stream_blocks_imply_fixed_payload :
  forall prog input witness stream halt_code,
    trace_stream_matches_witness stream witness ->
    trace_witness_fixed witness ->
    trace_stream_starts input stream ->
    trace_stream_steps prog witness stream ->
    trace_stream_halt witness halt_code ->
    exists fuel, FMFixedTracePayload prog input witness fuel.
Proof.
  intros prog input witness stream halt_code Hmatch Hfixed Hstart Hstep Hhalt.
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
        stream (S t) = code_trace_nth (S t) witness).
      {
        apply Hmatch.
        unfold fuel in Hle.
        lia.
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
    unfold trace_witness_last_code in Hhalted.
    unfold fuel in Hhalted.
    rewrite Hrun_nth in Hhalted.
    + exact Hhalted.
    + lia.
Qed.

(*
│
│          The valuation-level block predicates imply the existence of
│          a fixed payload by viewing code channels as a stream.
│
*)

(*       MatchWitness ∧ TraceWitnessFixed ∧ Start ∧ Step ∧ Halt ⇒ ∃ T.        *)
(*                        FixedPayload(prog,input,W,T)                        *)

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
  eapply trace_stream_blocks_imply_fixed_payload.
  - exact Hmatch.
  - exact Hfixed.
  - exact Hstart.
  - exact Hstep.
  - exact Hhalt.
Qed.

(*
│
│          Completeness: any satisfying valuation for the emitted
│          trace family reconstructs a valid FM trace witness.
│
*)

(*     FamilySat(TraceFamily(prog,input,W)) ⇒ FMValidTrace(prog,input,W)      *)

Lemma emit_trace_family_complete :
  forall prog input witness,
    family_satisfiable (emit_trace_family prog input witness) ->
    FMValidTrace prog input witness.
Proof.
  intros prog input witness Hsat.
  apply (proj1 (family_satisfiable_iff (emit_trace_family prog input witness))) in Hsat.
  destruct Hsat as [rho Hsat].
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

(*
│
│          The fixed-witness correctness theorem: the raw FM witness
│          is valid exactly when the emitted family is satisfiable.
│
*)

(*     FMValidTrace(prog,input,W) ⇔ FamilySat(TraceFamily(prog,input,W))      *)

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

(*
│
│          The concrete trace-family emitter satisfies the
│          well-formedness contract.
│
*)

(*                           EmitterWF(TraceFamily)                           *)

Theorem emit_trace_family_meets_wf_contract :
  fixed_trace_family_emitter_wf emit_trace_family.
Proof.
  exact emit_trace_family_wf.
Qed.

(*
│
│          The concrete trace-family emitter satisfies the
│          fixed-payload correctness contract.
│
*)

(*                        PayloadCorrect(TraceFamily)                         *)

Theorem emit_trace_family_meets_payload_contract :
  fixed_trace_family_emitter_payload_correct emit_trace_family.
Proof.
  intros prog input witness.
  rewrite <- FMValidTrace_iff_exists_fixed_trace_payload.
  apply trace_family_correct.
Qed.

(*
│
│          The concrete trace-family emitter satisfies the public
│          correctness contract.
│
*)

(*                        EmitterCorrect(TraceFamily)                         *)

Theorem emit_trace_family_meets_contract :
  fixed_trace_family_emitter_correct emit_trace_family.
Proof.
  exact trace_family_correct.
Qed.

(*
│
│          The concrete trace-family emitter satisfies the combined
│          well-formedness and correctness contract.
│
*)

(*                         EmitterWithWF(TraceFamily)                         *)

Theorem emit_trace_family_meets_contract_with_wf :
  fixed_trace_family_emitter_with_wf emit_trace_family.
Proof.
  intros prog input witness.
  split.
  - apply emit_trace_family_wf.
  - apply trace_family_correct.
Qed.

(*
│
│          The combined contract projects to the well-formedness
│          contract.
│
*)

(*                   EmitterWithWF(emit) ⇒ EmitterWF(emit)                    *)

Lemma fixed_trace_family_emitter_with_wf_wf :
  forall emit_trace,
    fixed_trace_family_emitter_with_wf emit_trace ->
    fixed_trace_family_emitter_wf emit_trace.
Proof.
  intros emit_trace Hcontract prog input witness.
  exact (proj1 (Hcontract prog input witness)).
Qed.

(*
│
│          The combined contract projects to the public correctness
│          contract.
│
*)

(*                 EmitterWithWF(emit) ⇒ EmitterCorrect(emit)                 *)

Lemma fixed_trace_family_emitter_with_wf_correct :
  forall emit_trace,
    fixed_trace_family_emitter_with_wf emit_trace ->
    fixed_trace_family_emitter_correct emit_trace.
Proof.
  intros emit_trace Hcontract prog input witness.
  exact (proj2 (Hcontract prog input witness)).
Qed.
