(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This layer re-exports the structured Fibonacci-machine ISA from `D001_04` into the P002 namespace and packages the machine syntax facts that later arithmetization files use.]]@*)

(*@doc.pl@[[P002 does not redefine the machine. It reflects the proved D001 hardware surface so later polynomial emitters can target a stable local API.]]@*)

(*@head.end@*)

From P002 Require Export P002_03__State_Codec.

Definition MachineCounter : Type := counter.
Definition MachineInstruction : Type := instruction.
Definition MachineProgram : Type := program.

Definition counter_tag (c : MachineCounter) : nat :=
  match c with
  | Counter1 => 1
  | Counter2 => 2
  end.

Definition instruction_tag (ins : MachineInstruction) : nat :=
  match ins with
  | INC _ _ => 0
  | JZDEC _ _ _ => 1
  | HALT => 2
  end.

Definition instruction_counter (ins : MachineInstruction) : option MachineCounter :=
  match ins with
  | INC c _ => Some c
  | JZDEC c _ _ => Some c
  | HALT => None
  end.

Definition instruction_arg1 (ins : MachineInstruction) : option nat :=
  match ins with
  | INC _ next_ip => Some next_ip
  | JZDEC _ zero_ip _ => Some zero_ip
  | HALT => None
  end.

Definition instruction_arg2 (ins : MachineInstruction) : option nat :=
  match ins with
  | INC _ _ => None
  | JZDEC _ _ dec_ip => Some dec_ip
  | HALT => None
  end.

(*@inline@[[The tag and projection helpers in this file are purely descriptive. They do not change the FM instruction set imported from D001; they expose small arithmetic handles that later P002 emitters can inspect without pattern matching on the full inductive syntax each time.]]@*)
(*@unicodemath@[[instruction\_tag : \mathcal I \to \{0,1,2\},\qquad counter\_tag : \mathcal C \to \{1,2\}.]]@*)

Definition fetch_instruction_at (prog : MachineProgram) (ip : nat)
  : option MachineInstruction :=
  nth_error prog ip.

Lemma counter_tag_nonzero :
  forall c,
    counter_tag c <> 0.
Proof.
  intros [|]; discriminate.
Qed.

Lemma counter_tag_injective :
  forall c1 c2,
    counter_tag c1 = counter_tag c2 ->
    c1 = c2.
Proof.
  intros c1 c2 Htag.
  destruct c1, c2; simpl in Htag; try discriminate; reflexivity.
Qed.

Lemma counter_eqb_reflect :
  forall c1 c2,
    counter_eqb c1 c2 = true <-> c1 = c2.
Proof.
  exact counter_eqb_correct.
Qed.

Lemma fetch_instruction_at_state :
  forall prog st,
    fetch_instruction_at prog (state_ip st) = nth_error prog (state_ip st).
Proof.
  reflexivity.
Qed.

(*@inline@[[`fetch_instruction_at` is the ROM-facing lookup primitive used by the later transition arithmetization. It makes the program counter explicit as a raw natural index while remaining definitionally equal to the underlying `nth_error` access.]]@*)
(*@unicodemath@[[fetch\_instruction\_at(prog,ip)=prog[ip]\ \text{(partial lookup in ROM)}.]]@*)

Lemma instruction_tag_cases :
  forall ins,
    instruction_tag ins <= 2.
Proof.
  intros [c next_ip|c zero_ip dec_ip|]; simpl; lia.
Qed.

Lemma instruction_counter_none_iff_halt :
  forall ins,
    instruction_counter ins = None <-> ins = HALT.
Proof.
  intros [c next_ip|c zero_ip dec_ip|]; simpl; split; intro H; try discriminate; try reflexivity.
Qed.

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

Lemma read_counter_write_counter_same :
  forall c v st,
    read_counter c (write_counter c v st) = v.
Proof.
  exact read_write_same.
Qed.

Lemma read_counter_write_counter_other :
  forall c1 c2 v st,
    c1 <> c2 ->
    read_counter c1 (write_counter c2 v st) = read_counter c1 st.
Proof.
  exact read_write_other.
Qed.

Lemma read_counter_set_ip :
  forall c ip st,
    read_counter c (set_ip ip st) = read_counter c st.
Proof.
  exact read_set_ip.
Qed.

Lemma state_ip_write_counter_bridge :
  forall c v st,
    state_ip (write_counter c v st) = state_ip st.
Proof.
  exact state_ip_write_counter.
Qed.

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

(*@inline@[[The initial-state lemmas are the entry point from external input into the FM semantics. They pin down the concrete start configuration that later trace predicates and compiler correctness statements must reproduce arithmetically.]]@*)
(*@unicodemath@[[initial\_state(input)=(1,input,0),\qquad initial\_state2(r_1,r_2)=(1,r_1,r_2).]]@*)

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

Lemma set_ip_preserves_well_formed :
  forall st ip,
    state_well_formed st ->
    ip < ip_limit ->
    state_well_formed (set_ip ip st).
Proof.
  exact state_well_formed_set_ip.
Qed.

Lemma initial_state_wf_bridge :
  forall input,
    input < r1_limit ->
    state_well_formed (initial_state input).
Proof.
  exact initial_state_well_formed.
Qed.

Lemma initial_state2_wf_bridge :
  forall r1 r2,
    r1 < r1_limit ->
    r2 < r2_limit ->
    state_well_formed (initial_state2 r1 r2).
Proof.
  exact initial_state2_well_formed.
Qed.
