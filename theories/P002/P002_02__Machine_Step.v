(*P002_02__Machine_Step.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / P002_02__Machine_Step                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer exposes the FM instruction interface, encoded one-step dynamics,
  and selector-gated cubic atoms used by the trace compiler.

  P002 does not redefine the machine. It gives the imported D001 transition
  system stable local names and proves the small arithmetic facts needed by
  later emitters.

*)

From P002 Require Export P002_01__Architecture.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                            MACHINE INTERFACE                            ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The local counter type is exactly the counter syntax
│          imported from D001.
│
*)

(*                          MachineCounter ≔ Counter                          *)

Definition MachineCounter : Type := counter.

(*
│
│          The local instruction type is exactly the instruction
│          syntax imported from D001.
│
*)

(*                      MachineInstruction ≔ Instruction                      *)

Definition MachineInstruction : Type := instruction.

(*
│
│          The local program type is exactly the finite instruction
│          table imported from D001.
│
*)

(*                          MachineProgram ≔ Program                          *)

Definition MachineProgram : Type := program.

(*
│
│          Counters are tagged by the two positive natural codes used
│          by later arithmetic tests.
│
*)

(*                              CounterTag(C₁)=1                              *)
(*                              CounterTag(C₂)=2                              *)

Definition counter_tag (c : MachineCounter) : nat :=
  match c with
  | Counter1 => 1
  | Counter2 => 2
  end.

(*
│
│          Instructions are tagged by their finite-control
│          constructor: increment, zero-test/decrement, or halt.
│
*)

(*                           InstructionTag(INC)=0                            *)
(*                          InstructionTag(JZDEC)=1                           *)
(*                           InstructionTag(HALT)=2                           *)

Definition instruction_tag (ins : MachineInstruction) : nat :=
  match ins with
  | INC _ _ => 0
  | JZDEC _ _ _ => 1
  | HALT => 2
  end.

(*
│
│          The counter projection records which register an
│          instruction reads or writes, if any.
│
*)

(*                            CounterOf(HALT)=None                            *)

Definition instruction_counter (ins : MachineInstruction) : option MachineCounter :=
  match ins with
  | INC c _ => Some c
  | JZDEC c _ _ => Some c
  | HALT => None
  end.

(*
│
│          The first numeric argument is the next instruction pointer
│          for `INC` and the zero branch target for `JZDEC`.
│
*)

(*                              Arg₁(INC(c,q))=q                              *)
(*                          Arg₁(JZDEC(c,q₀,q₁))=q₀                           *)

Definition instruction_arg1 (ins : MachineInstruction) : option nat :=
  match ins with
  | INC _ next_ip => Some next_ip
  | JZDEC _ zero_ip _ => Some zero_ip
  | HALT => None
  end.

(*
│
│          The second numeric argument exists only for `JZDEC`; it is
│          the positive-branch target.
│
*)

(*                          Arg₂(JZDEC(c,q₀,q₁))=q₁                           *)
(*                               Arg₂(INC)=None                               *)
(*                              Arg₂(HALT)=None                               *)

Definition instruction_arg2 (ins : MachineInstruction) : option nat :=
  match ins with
  | INC _ _ => None
  | JZDEC _ _ dec_ip => Some dec_ip
  | HALT => None
  end.

(*
│
│          Program lookup is the ROM-facing primitive used by later
│          transition arithmetization. It makes the program counter
│          explicit as a raw natural index while remaining
│          definitionally equal to `nth_error`.
│
*)

(*                          Fetch(prog,ip)=prog⟦ip⟧                           *)

Definition fetch_instruction_at (prog : MachineProgram) (ip : nat)
  : option MachineInstruction :=
  nth_error prog ip.

(*
│
│          Counter tags are never zero. This separates them from the
│          halted instruction pointer code.
│
*)

(*                             CounterTag(c) ≠ 0                              *)

Lemma counter_tag_nonzero :
  forall c,
    counter_tag c <> 0.
Proof.
  intros [|]; discriminate.
Qed.

(*
│
│          The counter tag map distinguishes the two counters.
│
*)

(*                   CounterTag(c₁)=CounterTag(c₂) ⇒ c₁=c₂                    *)

Lemma counter_tag_injective :
  forall c1 c2,
    counter_tag c1 = counter_tag c2 ->
    c1 = c2.
Proof.
  intros c1 c2 Htag.
  destruct c1, c2; simpl in Htag; try discriminate; reflexivity.
Qed.

(*
│
│          The executable counter comparison is logically exact.
│
*)

(*                       CounterEqB(c₁,c₂)=true ⇔ c₁=c₂                       *)

Lemma counter_eqb_reflect :
  forall c1 c2,
    counter_eqb c1 c2 = true <-> c1 = c2.
Proof.
  exact counter_eqb_correct.
Qed.

(*
│
│          Fetching at the instruction pointer of a state is just list
│          lookup at that pointer.
│
*)

(*                       FetchAt(prog,st)=prog⟦IP(st)⟧                        *)

Lemma fetch_instruction_at_state :
  forall prog st,
    fetch_instruction_at prog (state_ip st) = nth_error prog (state_ip st).
Proof.
  reflexivity.
Qed.

(*
│
│          Instruction tags lie in the finite three-element range.
│
*)

(*                          InstructionTag(ins) ≤ 2                           *)

Lemma instruction_tag_cases :
  forall ins,
    instruction_tag ins <= 2.
Proof.
  intros [c next_ip|c zero_ip dec_ip|]; simpl; lia.
Qed.

(*
│
│          An instruction has no counter projection exactly when it is
│          `HALT`.
│
*)

(*                       CounterOf(ins)=None ⇔ ins=HALT                       *)

Lemma instruction_counter_none_iff_halt :
  forall ins,
    instruction_counter ins = None <-> ins = HALT.
Proof.
  intros [c next_ip|c zero_ip dec_ip|]; simpl; split; intro H; try discriminate; try reflexivity.
Qed.

(*
│
│          If an instruction projects a counter, it is either an
│          increment or a zero-test/decrement instruction on that
│          counter.
│
*)

(*         CounterOf(ins)=Some(c) ⇒ ins=INC(c,q) ∨ ins=JZDEC(c,q₀,q₁)         *)

Lemma instruction_counter_some_cases :
  forall ins c,
    instruction_counter ins = Some c ->
    (exists next_ip, ins = INC c next_ip) \/
    (exists zero_ip dec_ip, ins = JZDEC c zero_ip dec_ip).
Proof.
  intros [c' next_ip|c' zero_ip dec_ip|] c Hcounter; simpl in Hcounter.
  - inversion Hcounter; subst c.
    left.
    exists next_ip.
    reflexivity.
  - inversion Hcounter; subst c.
    right.
    exists zero_ip, dec_ip.
    reflexivity.
  - discriminate.
Qed.

(*
│
│          Reading the same counter after writing it returns the
│          written value.
│
*)

(*                          Read(c,Write(c,v,st))=v                           *)

Lemma read_counter_write_counter_same :
  forall c v st,
    read_counter c (write_counter c v st) = v.
Proof.
  exact read_write_same.
Qed.

(*
│
│          Writing one counter leaves the other counter unchanged.
│
*)

(*                c₁≠c₂ ⇒ Read(c₁,Write(c₂,v,st))=Read(c₁,st)                 *)

Lemma read_counter_write_counter_other :
  forall c1 c2 v st,
    c1 <> c2 ->
    read_counter c1 (write_counter c2 v st) = read_counter c1 st.
Proof.
  exact read_write_other.
Qed.

(*
│
│          Changing the instruction pointer does not change either
│          counter.
│
*)

(*                       Read(c,SetIP(q,st))=Read(c,st)                       *)

Lemma read_counter_set_ip :
  forall c ip st,
    read_counter c (set_ip ip st) = read_counter c st.
Proof.
  exact read_set_ip.
Qed.

(*
│
│          Writing a counter does not change the instruction pointer.
│
*)

(*                          IP(Write(c,v,st))=IP(st)                          *)

Lemma state_ip_write_counter_bridge :
  forall c v st,
    state_ip (write_counter c v st) = state_ip st.
Proof.
  exact state_ip_write_counter.
Qed.

(*
│
│          The one-input initial state starts at instruction pointer
│          `1`, places the input in register one, and clears register
│          two.
│
*)

(*                         Initial(input)=(1,input,0)                         *)

Lemma initial_state_components :
  forall input,
    state_ip (initial_state input) = 1 /\
    state_r1 (initial_state input) = input /\
    state_r2 (initial_state input) = 0.
Proof.
  intros input.
  unfold initial_state.
  simpl.
  auto.
Qed.

(*
│
│          The two-register initial state starts at instruction
│          pointer `1` and stores the two provided register values.
│
*)

(*                         Initial₂(r₁,r₂)=(1,r₁,r₂)                          *)

Lemma initial_state2_components :
  forall r1 r2,
    state_ip (initial_state2 r1 r2) = 1 /\
    state_r1 (initial_state2 r1 r2) = r1 /\
    state_r2 (initial_state2 r1 r2) = r2.
Proof.
  intros r1 r2.
  unfold initial_state2.
  simpl.
  auto.
Qed.

(*
│
│          Writing a bounded counter value preserves state
│          well-formedness.
│
*)

(*                 WF(st) ∧ v < Limit(c) ⇒ WF(Write(c,v,st))                  *)

Lemma write_counter_preserves_well_formed :
  forall st c v,
    state_well_formed st ->
    (match c with
     | Counter1 => v < r1_limit
     | Counter2 => v < r2_limit
     end) ->
    state_well_formed (write_counter c v st).
Proof.
  exact state_well_formed_write_counter.
Qed.

(*
│
│          Setting a bounded instruction pointer preserves state
│          well-formedness.
│
*)

(*                   WF(st) ∧ q < IPLimit ⇒ WF(SetIP(q,st))                   *)

Lemma set_ip_preserves_well_formed :
  forall st ip,
    state_well_formed st ->
    ip < ip_limit ->
    state_well_formed (set_ip ip st).
Proof.
  exact state_well_formed_set_ip.
Qed.

(*
│
│          A bounded one-input initial state is well-formed.
│
*)

(*                    input < R1Limit ⇒ WF(Initial(input))                    *)

Lemma initial_state_wf_bridge :
  forall input,
    input < r1_limit ->
    state_well_formed (initial_state input).
Proof.
  exact initial_state_well_formed.
Qed.

(*
│
│          A bounded two-register initial state is well-formed.
│
*)

(*             r₁ < R1Limit ∧ r₂ < R2Limit ⇒ WF(Initial₂(r₁,r₂))              *)

Lemma initial_state2_wf_bridge :
  forall r1 r2,
    r1 < r1_limit ->
    r2 < r2_limit ->
    state_well_formed (initial_state2 r1 r2).
Proof.
  exact initial_state2_well_formed.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                           TRANSITION RELATION                           ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          Encoded states are natural-number state codes.
│
*)

(*                              EncodedState ≔ ℕ                              *)

Definition EncodedState : Type := nat.

(*
│
│          The current structured state is obtained by decoding the
│          numeric state code.
│
*)

(*                       CurrentState(s)=DecodeState(s)                       *)

Definition current_state (s : EncodedState) : MachineState :=
  decode_state s.

(*
│
│          The current instruction is fetched from the decoded state
│          and program table.
│
*)

(*           CurrentInstruction(prog,s)=Fetch(prog,CurrentState(s))           *)

Definition current_instruction (prog : MachineProgram) (s : EncodedState)
  : option MachineInstruction :=
  fetch_instruction prog (current_state s).

(*
│
│          A structured state is halted exactly when its instruction
│          pointer is zero, exposed here as a boolean test.
│
*)

(*                      HaltedStateB(st)=true ⇔ IP(st)=0                      *)

Definition halted_state_b (st : MachineState) : bool :=
  Nat.eqb (state_ip st) 0.

(*
│
│          The code-level halt test decodes the state code before
│          applying the structured halt test.
│
*)

(*                HaltedCodeB(s)=HaltedStateB(DecodeState(s))                 *)

Definition halted_code_b (s : EncodedState) : bool :=
  halted_state_b (current_state s).

(*
│
│          The code-level zero-counter test decodes the state code and
│          reads the selected counter.
│
*)

(*             ZeroCounterB(c,s)=true ⇔ Read(c,DecodeState(s))=0              *)

Definition counter_zero_code_b (c : MachineCounter) (s : EncodedState) : bool :=
  Nat.eqb (read_counter c (current_state s)) 0.

(*
│
│          Structured stepping is the imported D001 step function
│          under the local P002 name.
│
*)

(*                 StepState(prog,st)=D001StepState(prog,st)                  *)

Definition StepState : MachineProgram -> MachineState -> MachineState :=
  step_state.

(*
│
│          Code-level stepping is the imported D001 next-state
│          function on encoded states.
│
*)

(*                     StepCode(prog,s)=NextState(prog,s)                     *)

Definition StepCode : MachineProgram -> EncodedState -> EncodedState :=
  NextState.

(*
│
│          The code-level step relation is the imported graph of the
│          deterministic next-state function.
│
*)

(*                StepRelation(prog,s,t) ⇔ t=StepCode(prog,s)                 *)

Definition StepRelation (prog : MachineProgram)
    (s t : EncodedState) : Prop :=
  step_relation prog s t.

(*
│
│          The structured step relation is the imported graph of
│          structured machine stepping.
│
*)

(*                       StepRelationState(prog,st,st′)                       *)

Definition StepRelationState (prog : MachineProgram)
    (st st' : MachineState) : Prop :=
  step_state_relation prog st st'.

(*
│
│          The executable step matcher is the boolean reflection of
│          the code-level step relation.
│
*)

(*            StepMatchesB(prog,s,t)=true ⇔ StepRelation(prog,s,t)            *)

Definition step_matches_b (prog : MachineProgram)
    (s t : EncodedState) : bool :=
  stepb prog s t.

(*
│
│          The current-state projection is definitionally decoding.
│
*)

(*                       CurrentState(s)=DecodeState(s)                       *)

Lemma current_state_eq :
  forall s,
    current_state s = decode_state s.
Proof.
  reflexivity.
Qed.

(*
│
│          Current-instruction lookup reduces to fetching at the
│          decoded state.
│
*)

(*           CurrentInstruction(prog,s)=Fetch(prog,DecodeState(s))            *)

Lemma current_instruction_eq :
  forall prog s,
    current_instruction prog s = fetch_instruction prog (decode_state s).
Proof.
  reflexivity.
Qed.

(*
│
│          The structured halt boolean is logically exact.
│
*)

(*                  HaltedStateB(st)=true ⇔ HaltedState(st)                   *)

Lemma halted_state_b_correct :
  forall st,
    halted_state_b st = true <-> halted_state st.
Proof.
  intros st.
  unfold halted_state_b, halted_state.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

(*
│
│          The code-level halt boolean is logically exact after
│          decoding.
│
*)

(*             HaltedCodeB(s)=true ⇔ HaltedState(DecodeState(s))              *)

Lemma halted_code_b_correct :
  forall s,
    halted_code_b s = true <-> halted_state (decode_state s).
Proof.
  intros s.
  unfold halted_code_b.
  rewrite current_state_eq.
  apply halted_state_b_correct.
Qed.

(*
│
│          The code-level zero-counter boolean is logically exact
│          after decoding.
│
*)

(*             ZeroCounterB(c,s)=true ⇔ Read(c,DecodeState(s))=0              *)

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

(*
│
│          Every structured state steps to `StepState prog st` in the
│          structured step relation.
│
*)

(*               StepRelationState(prog,st,StepState(prog,st))                *)

Lemma step_state_relation_step_bridge :
  forall prog st,
    StepRelationState prog st (StepState prog st).
Proof.
  exact step_state_relation_step.
Qed.

(*
│
│          Every encoded state steps to `StepCode prog s` in the
│          code-level step relation.
│
*)

(*                   StepRelation(prog,s,StepCode(prog,s))                    *)

Lemma step_relation_next_bridge :
  forall prog s,
    StepRelation prog s (StepCode prog s).
Proof.
  exact step_relation_next.
Qed.

(*
│
│          The executable step matcher reflects the code-level step
│          relation.
│
*)

(*            StepMatchesB(prog,s,t)=true ⇔ StepRelation(prog,s,t)            *)

Lemma step_matches_b_correct :
  forall prog s t,
    step_matches_b prog s t = true <-> StepRelation prog s t.
Proof.
  exact stepb_correct.
Qed.

(*
│
│          The code-level step relation is total.
│
*)

(*                        ∃ t. StepRelation(prog,s,t)                         *)

Lemma step_relation_total_bridge :
  forall prog s,
    exists t, StepRelation prog s t.
Proof.
  exact step_total.
Qed.

(*
│
│          A halted structured state is fixed by structured stepping.
│
*)

(*                  HaltedState(st) ⇒ StepState(prog,st)=st                   *)

Lemma halted_state_fixed_bridge :
  forall prog st,
    halted_state st ->
    StepState prog st = st.
Proof.
  exact halted_state_fixed.
Qed.

(*
│
│          Structured stepping is deterministic.
│
*)

(* StepRelationState(prog,st,st₁) ∧ StepRelationState(prog,st,st₂) ⇒ st₁=st₂  *)

Lemma step_state_deterministic_bridge :
  forall prog st st1 st2,
    StepRelationState prog st st1 ->
    StepRelationState prog st st2 ->
    st1 = st2.
Proof.
  exact step_state_deterministic.
Qed.

(*
│
│          On well-formed image points, code-level stepping agrees
│          with structured stepping followed by re-encoding.
│
*)

(* WF(st) ⇒ StepCode(prog,EncodeState(st)) = EncodeState(StepState(prog,st))  *)

Lemma next_state_on_encoded_state_bridge :
  forall prog st,
    state_well_formed st ->
    StepCode prog (encode_state st) = encode_state (StepState prog st).
Proof.
  exact NextState_on_encoded_state.
Qed.

(*
│
│          If the code-level halt test succeeds, the decoded
│          instruction pointer is zero.
│
*)

(*                HaltedCodeB(s)=true ⇒ IP(CurrentState(s))=0                 *)

Lemma current_instruction_halted_ip0 :
  forall s,
    halted_code_b s = true ->
    state_ip (current_state s) = 0.
Proof.
  intros s Hhalt.
  apply halted_code_b_correct in Hhalt.
  exact Hhalt.
Qed.

(*
│
│          The step relation graph determines exactly the value of
│          `StepCode`.
│
*)

(*                StepRelation(prog,s,t) ⇒ t=StepCode(prog,s)                 *)

Lemma step_code_total_function :
  forall prog s t,
    StepRelation prog s t ->
    t = StepCode prog s.
Proof.
  intros prog s t Hstep.
  exact Hstep.
Qed.

(*
│
│          The code-level step relation has unique targets.
│
*)

(*         StepRelation(prog,s,t₁) ∧ StepRelation(prog,s,t₂) ⇒ t₁=t₂          *)

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

(*
│
│          The executable step matcher accepts the reflexive graph
│          point generated by `StepCode`.
│
*)

(*                 StepMatchesB(prog,s,StepCode(prog,s))=true                 *)

Lemma step_matches_b_refl :
  forall prog s,
    step_matches_b prog s (StepCode prog s) = true.
Proof.
  intros prog s.
  apply step_matches_b_correct.
  apply step_relation_next_bridge.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                           STEP ARITHMETIZATION                          ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The source-state decoder exposes the structured state read
│          from a source code.
│
*)

(*                       SourceState(s)=DecodeState(s)                        *)

Definition SourceState : EncodedState -> MachineState := source_state.

(*
│
│          The target-state decoder exposes the structured state read
│          from a target code.
│
*)

(*                       TargetState(t)=DecodeState(t)                        *)

Definition TargetState : EncodedState -> MachineState := target_state.

(*
│
│          The instruction-pointer observation tests whether the
│          decoded source state is at a given control location.
│
*)

(*                IPMatchesB(q,s)=true ⇔ IP(DecodeState(s))=q                 *)

Definition ip_matches_b (q : nat) (s : EncodedState) : bool := ip_eqb q s.

(*
│
│          The counter-zero observation tests whether the selected
│          decoded source counter is zero.
│
*)

(*             CounterZeroB(c,s)=true ⇔ Read(c,DecodeState(s))=0              *)

Definition counter_zero_obs_b (c : MachineCounter) (s : EncodedState) : bool :=
  counter_zero_b c s.

(*
│
│          The target-instruction-pointer observation tests the
│          decoded target state against a branch target.
│
*)

(*                 TargetIPB(q,t)=true ⇔ IP(DecodeState(t))=q                 *)

Definition target_ip_matches_b (q : nat) (t : EncodedState) : bool :=
  target_ipb q t.

(*
│
│          The successor observation tests that a selected counter
│          increased by one across the step.
│
*)

(* CounterSuccB(c,s,t)=true ⇔ Read(c,DecodeState(t))=Read(c,DecodeState(s))+1 *)

Definition counter_succ_obs_b
    (c : MachineCounter) (s t : EncodedState) : bool :=
  counter_succ_b c s t.

(*
│
│          The predecessor observation tests that a selected counter
│          decreased by one across the step.
│
*)

(* CounterPredB(c,s,t)=true ⇔ Read(c,DecodeState(s))=Read(c,DecodeState(t))+1 *)

Definition counter_pred_obs_b
    (c : MachineCounter) (s t : EncodedState) : bool :=
  counter_pred_b c s t.

(*
│
│          The frozen-counter observation tests that the non-selected
│          counter is unchanged across the step.
│
*)

(*                         FrozenOtherB(c,s,t)=true ⇔                         *)
(*       OtherCounter(c,DecodeState(s))=OtherCounter(c,DecodeState(t))        *)

Definition frozen_other_counter_obs_b
    (c : MachineCounter) (s t : EncodedState) : bool :=
  frozen_other_counter_b c s t.

(*
│
│          The variable bound for a unary selector atom covers the
│          selector and one observed variable.
│
*)

(*                         SelectorWF(a,x)=1+max(a,x)                         *)

Definition selector_var_wf (selector x : nat) : nat :=
  S (Nat.max selector x).

(*
│
│          The variable bound for a binary selector atom covers the
│          selector and two observed variables.
│
*)

(*                      SelectorWF₂(a,x,y)=1+max(a,x,y)                       *)

Definition selector_binary_var_wf (selector x y : nat) : nat :=
  S (Nat.max selector (Nat.max x y)).

(*
│
│          The zero selector atom says that, when selector `a` is
│          active, the selected value `x` must be zero.
│
*)

(*                           ZeroAtom(a,x) : a·x=0                            *)

Definition emit_selector_zero_eq (selector x : nat) : h10_nd3n_equation :=
  {|
    var_count := selector_var_wf selector x;
    lhs_terms := [{| coeff := 1; mono := m_quadratic selector x |}];
    rhs_terms := []
  |}.

(*
│
│          The same-value selector atom says that, when selector `a`
│          is active, two selected values must agree.
│
*)

(*                         SameAtom(a,x,y) : a·x=a·y                          *)

Definition emit_selector_same_eq (selector x y : nat) : h10_nd3n_equation :=
  {|
    var_count := selector_binary_var_wf selector x y;
    lhs_terms := [{| coeff := 1; mono := m_quadratic selector x |}];
    rhs_terms := [{| coeff := 1; mono := m_quadratic selector y |}]
  |}.

(*
│
│          The successor selector atom says that, when selector `a` is
│          active, `target` is the successor of `source`.
│
*)

(*                        SuccAtom(a,t,s) : a·t=a+a·s                         *)

Definition emit_selector_succ_eq (selector target source : nat)
  : h10_nd3n_equation :=
  {|
    var_count := selector_binary_var_wf selector target source;
    lhs_terms := [{| coeff := 1; mono := m_quadratic selector target |}];
    rhs_terms :=
      [{| coeff := 1; mono := m_linear selector |};
       {| coeff := 1; mono := m_quadratic selector source |}]
  |}.

(*
│
│          The predecessor selector atom is implemented by reversing
│          the source and target positions of the successor atom.
│
*)

(*                     PredAtom(a,s,t) ≔ SuccAtom(a,s,t)                      *)

Definition emit_selector_pred_eq (selector source target : nat)
  : h10_nd3n_equation :=
  emit_selector_succ_eq selector source target.

(*
│
│          The product-zero selector atom says that, when selector `a`
│          is active, at least one of the two selected values is zero.
│
*)

(*                      ProductZeroAtom(a,x,y) : a·x·y=0                      *)

Definition emit_selector_product_zero_eq (selector x y : nat)
  : h10_nd3n_equation :=
  {|
    var_count := selector_binary_var_wf selector x y;
    lhs_terms := [{| coeff := 1; mono := m_cubic selector x y |}];
    rhs_terms := []
  |}.

(*
│
│          A one-term polynomial evaluates to the value of its only
│          term. This local lemma duplicates the architecture-layer
│          singleton fact while preserving the existing
│          selector-section name.
│
*)

Lemma eval_poly_singleton_term :
  forall (t : term) (rho : valuation),
    eval_poly [t] rho = eval_term rho t.
Proof.
  intros t rho.
  unfold eval_poly.
  simpl.
  lia.
Qed.

(*
│
│          The zero selector atom is well-scoped by its unary selector
│          bound.
│
*)

(*                             WF(ZeroAtom(a,x))                              *)

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

(*
│
│          The same-value selector atom is well-scoped by its binary
│          selector bound.
│
*)

(*                            WF(SameAtom(a,x,y))                             *)

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

(*
│
│          The successor selector atom is well-scoped by its binary
│          selector bound.
│
*)

(*                            WF(SuccAtom(a,t,s))                             *)

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

(*
│
│          The product-zero selector atom is well-scoped by its binary
│          selector bound.
│
*)

(*                         WF(ProductZeroAtom(a,x,y))                         *)

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

(*
│
│          When the selector is active, the zero atom enforces that
│          the selected value is zero.
│
*)

(*                 ρ(a)=1 ⇒ Solves(ZeroAtom(a,x),ρ) ⇔ ρ(x)=0                  *)

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

(*
│
│          When the selector is inactive, the zero atom is vacuous.
│
*)

(*                      ρ(a)=0 ⇒ Solves(ZeroAtom(a,x),ρ)                      *)

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

(*
│
│          When the selector is active, the same-value atom enforces
│          equality of the selected values.
│
*)

(*               ρ(a)=1 ⇒ Solves(SameAtom(a,x,y),ρ) ⇔ ρ(x)=ρ(y)               *)

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

(*
│
│          When the selector is inactive, the same-value atom is
│          vacuous.
│
*)

(*                     ρ(a)=0 ⇒ Solves(SameAtom(a,x,y),ρ)                     *)

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

(*
│
│          When the selector is active, the successor atom enforces
│          `target = source + 1`.
│
*)

(*              ρ(a)=1 ⇒ Solves(SuccAtom(a,t,s),ρ) ⇔ ρ(t)=ρ(s)+1              *)

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

(*
│
│          When the selector is inactive, the successor atom is
│          vacuous.
│
*)

(*                     ρ(a)=0 ⇒ Solves(SuccAtom(a,t,s),ρ)                     *)

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

(*
│
│          When the selector is active, the predecessor atom enforces
│          `source = target + 1`.
│
*)

(*              ρ(a)=1 ⇒ Solves(PredAtom(a,s,t),ρ) ⇔ ρ(s)=ρ(t)+1              *)

Lemma emit_selector_pred_eq_active :
  forall rho selector source target,
    rho selector = 1 ->
    solves (emit_selector_pred_eq selector source target) rho <->
    rho source = S (rho target).
Proof.
  exact emit_selector_succ_eq_active.
Qed.

(*
│
│          When the selector is active, the product-zero atom enforces
│          that at least one selected value is zero.
│
*)

(*        ρ(a)=1 ⇒ Solves(ProductZeroAtom(a,x,y),ρ) ⇔ ρ(x)=0 ∨ ρ(y)=0         *)

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

(*
│
│          When the selector is inactive, the product-zero atom is
│          vacuous.
│
*)

(*                 ρ(a)=0 ⇒ Solves(ProductZeroAtom(a,x,y),ρ)                  *)

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

(*
│
│          The instruction-pointer observation boolean reflects the
│          decoded source instruction pointer.
│
*)

(*                IPMatchesB(q,s)=true ⇔ IP(DecodeState(s))=q                 *)

Lemma ip_matches_b_correct_bridge :
  forall q s,
    ip_matches_b q s = true <-> state_ip (decode_state s) = q.
Proof.
  exact ip_eqb_correct.
Qed.

(*
│
│          The counter-zero observation boolean reflects the selected
│          decoded source counter being zero.
│
*)

(*             CounterZeroB(c,s)=true ⇔ Read(c,DecodeState(s))=0              *)

Lemma counter_zero_obs_b_correct_bridge :
  forall c s,
    counter_zero_obs_b c s = true <->
    read_counter c (decode_state s) = 0.
Proof.
  exact counter_zero_b_correct.
Qed.

(*
│
│          The target-instruction-pointer observation boolean reflects
│          the decoded target instruction pointer.
│
*)

(*                 TargetIPB(q,t)=true ⇔ IP(DecodeState(t))=q                 *)

Lemma target_ip_matches_b_correct_bridge :
  forall q t,
    target_ip_matches_b q t = true <-> state_ip (decode_state t) = q.
Proof.
  exact target_ipb_correct.
Qed.

(*
│
│          The successor observation boolean reflects a one-step
│          counter increment across source and target codes.
│
*)

(* CounterSuccB(c,s,t)=true ⇔ Read(c,DecodeState(t))=Read(c,DecodeState(s))+1 *)

Lemma counter_succ_obs_b_correct_bridge :
  forall c s t,
    counter_succ_obs_b c s t = true <->
    read_counter c (decode_state t) =
    S (read_counter c (decode_state s)).
Proof.
  exact counter_succ_b_correct.
Qed.

(*
│
│          The predecessor observation boolean reflects a one-step
│          counter decrement across source and target codes.
│
*)

(* CounterPredB(c,s,t)=true ⇔ Read(c,DecodeState(s))=Read(c,DecodeState(t))+1 *)

Lemma counter_pred_obs_b_correct_bridge :
  forall c s t,
    counter_pred_obs_b c s t = true <->
    read_counter c (decode_state s) =
    S (read_counter c (decode_state t)).
Proof.
  exact counter_pred_b_correct.
Qed.

(*
│
│          The frozen-counter observation boolean reflects
│          preservation of the counter not selected by the
│          instruction.
│
*)

(*                         FrozenOtherB(c,s,t)=true ⇔                         *)
(*       OtherCounter(c,DecodeState(s))=OtherCounter(c,DecodeState(t))        *)

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

(*
│
│          The additive D001 theorem states that one well-formed
│          encoded step is the old code plus the instruction-pointer
│          and register deltas, after embedding in ℤ.
│
*)

(*                 WF(st) ⇒ StepCode(prog,EncodeState(st)) =                  *)
(*              EncodeState(st)+ΔIP(prog,st)+ΔR(prog,st) over ℤ               *)

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

(*
│
│          For a fetched halt instruction, the additive theorem
│          specializes to the halt instruction-pointer delta.
│
*)

(*           Fetch(prog,st)=HALT ⇒ StepCode(prog,EncodeState(st)) =           *)
(*                    EncodeState(st)+ΔIP(IP(st),0) over ℤ                    *)

Lemma HALT_additive_bridge :
  forall prog st,
    state_well_formed st ->
    fetch_instruction prog st = Some HALT ->
    Z.of_nat (StepCode prog (encode_state st)) =
    (Z.of_nat (encode_state st) + ip_delta (state_ip st) 0)%Z.
Proof.
  exact HALT_additive.
Qed.
