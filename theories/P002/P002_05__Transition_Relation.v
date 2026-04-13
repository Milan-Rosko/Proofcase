(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This layer reflects the one-step Fibonacci-machine transition from `D001_05` into the P002 namespace and packages the observation predicates that the later polynomial emitters target.]]@*)

(*@doc.pl@[[The step itself remains the proved D001 function. P002 adds only naming and bridge lemmas for encoded-state inspection.]]@*)

(*@head.end@*)

From P002 Require Export P002_04__Machine_Definition.

Definition EncodedState : Type := nat.

Definition current_state (s : EncodedState) : MachineState :=
  decode_state s.

Definition current_instruction (prog : MachineProgram) (s : EncodedState)
  : option MachineInstruction :=
  fetch_instruction prog (current_state s).

Definition halted_state_b (st : MachineState) : bool :=
  Nat.eqb (state_ip st) 0.

Definition halted_code_b (s : EncodedState) : bool :=
  halted_state_b (current_state s).

Definition counter_zero_code_b (c : MachineCounter) (s : EncodedState) : bool :=
  Nat.eqb (read_counter c (current_state s)) 0.

Definition StepState : MachineProgram -> MachineState -> MachineState :=
  step_state.

Definition StepCode : MachineProgram -> EncodedState -> EncodedState :=
  NextState.

Definition StepRelation (prog : MachineProgram)
    (s t : EncodedState) : Prop :=
  step_relation prog s t.

Definition StepRelationState (prog : MachineProgram)
    (st st' : MachineState) : Prop :=
  step_state_relation prog st st'.

Definition step_matches_b (prog : MachineProgram)
    (s t : EncodedState) : bool :=
  stepb prog s t.

(*@inline@[[This file works entirely with the projected external dynamics on encoded naturals. The current code `s` is first decoded to a structured FM state, one proved D001 step is executed there, and the result is re-encoded as the next external code.]]@*)
(*@unicodemath@[[StepCode(prog,s)=encode\_state(step\_state(prog,decode\_state(s))).]]@*)

Lemma current_state_eq :
  forall s,
    current_state s = decode_state s.
Proof.
  reflexivity.
Qed.

Lemma current_instruction_eq :
  forall prog s,
    current_instruction prog s = fetch_instruction prog (decode_state s).
Proof.
  reflexivity.
Qed.

Lemma halted_state_b_correct :
  forall st,
    halted_state_b st = true <-> halted_state st.
Proof.
  intros st.
  unfold halted_state_b, halted_state.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

Lemma halted_code_b_correct :
  forall s,
    halted_code_b s = true <-> halted_state (decode_state s).
Proof.
  intros s.
  unfold halted_code_b.
  rewrite current_state_eq.
  apply halted_state_b_correct.
Qed.

Lemma counter_zero_code_b_correct :
  forall c s,
    counter_zero_code_b c s = true <->
    read_counter c (decode_state s) = 0.
Proof.
  intros c s.
  unfold counter_zero_code_b.
  rewrite current_state_eq.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

Lemma step_state_relation_step_bridge :
  forall prog st,
    StepRelationState prog st (StepState prog st).
Proof.
  exact step_state_relation_step.
Qed.

(*@inline@[[The bridge lemmas here simply restate the proved D001 transition facts in P002 names. Their purpose is not new semantics but namespace stability for the later arithmetic compiler.]]@*)

Lemma step_relation_next_bridge :
  forall prog s,
    StepRelation prog s (StepCode prog s).
Proof.
  exact step_relation_next.
Qed.

Lemma step_matches_b_correct :
  forall prog s t,
    step_matches_b prog s t = true <-> StepRelation prog s t.
Proof.
  exact stepb_correct.
Qed.

Lemma step_relation_total_bridge :
  forall prog s,
    exists t, StepRelation prog s t.
Proof.
  exact step_total.
Qed.

Lemma halted_state_fixed_bridge :
  forall prog st,
    halted_state st ->
    StepState prog st = st.
Proof.
  exact halted_state_fixed.
Qed.

Lemma step_state_deterministic_bridge :
  forall prog st st1 st2,
    StepRelationState prog st st1 ->
    StepRelationState prog st st2 ->
    st1 = st2.
Proof.
  exact step_state_deterministic.
Qed.

Lemma next_state_on_encoded_state_bridge :
  forall prog st,
    state_well_formed st ->
    StepCode prog (encode_state st) = encode_state (StepState prog st).
Proof.
  exact NextState_on_encoded_state.
Qed.

(*@inline@[[`next_state_on_encoded_state_bridge` is the key compatibility fact for P002: on genuine FM image points, stepping at the code level agrees exactly with stepping the structured machine state and then re-encoding. This is the theorem that lets later polynomial constraints talk about a raw numeric successor while still meaning the intended machine transition.]]@*)
(*@unicodemath@[[state\_well\_formed(st)\Rightarrow StepCode(prog,encode\_state(st))=encode\_state(StepState(prog,st)).]]@*)

Lemma current_instruction_halted_ip0 :
  forall s,
    halted_code_b s = true ->
    state_ip (current_state s) = 0.
Proof.
  intros s Hhalt.
  apply halted_code_b_correct in Hhalt.
  exact Hhalt.
Qed.

Lemma step_code_total_function :
  forall prog s t,
    StepRelation prog s t ->
    t = StepCode prog s.
Proof.
  intros prog s t Hstep.
  exact Hstep.
Qed.

Lemma step_code_unique :
  forall prog s t1 t2,
    StepRelation prog s t1 ->
    StepRelation prog s t2 ->
    t1 = t2.
Proof.
  intros prog s t1 t2 H1 H2.
  unfold StepRelation in *.
  congruence.
Qed.

Lemma step_matches_b_refl :
  forall prog s,
    step_matches_b prog s (StepCode prog s) = true.
Proof.
  intros prog s.
  apply step_matches_b_correct.
  apply step_relation_next_bridge.
Qed.
