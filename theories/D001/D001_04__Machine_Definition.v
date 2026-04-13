(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This file defines the instruction set and basic state accessors of the Vector Iterant.]]@*)

(*@doc.pl@[[The machine is a two-counter Minsky-style kernel operating over the band-coded state space developed in the preceding files.]]@*)

(*@head.end@*)

From D001 Require Export D001_03__State_Codec.

Inductive counter : Type :=
| Counter1
| Counter2.

Inductive instruction : Type :=
| INC : counter -> nat -> instruction
| JZDEC : counter -> nat -> nat -> instruction
| HALT : instruction.

(*@inline@[[A `program` is a ROM list of instructions indexed by the machine's instruction pointer.]]@*)

Definition program : Type := list instruction.

Definition counter_eqb (c1 c2 : counter) : bool :=
  match c1, c2 with
  | Counter1, Counter1 => true
  | Counter2, Counter2 => true
  | _, _ => false
  end.

(*@inline@[[`counter_eqb_correct` turns the machine's boolean counter test into propositional equality, so later proofs can pass cleanly between executable case analyses and logical reasoning.]]@*)

(*@unicodemath@[[counter_eqb(c1, c2) = true ⇔ c1 = c2.]]@*)

Lemma counter_eqb_correct :
  forall c1 c2,
    counter_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2.
  destruct c1, c2; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

Definition read_counter (c : counter) (st : FMState) : nat :=
  match c with
  | Counter1 => state_r1 st
  | Counter2 => state_r2 st
  end.

Definition write_counter (c : counter) (v : nat) (st : FMState) : FMState :=
  match c with
  | Counter1 => Build_FMState (state_ip st) v (state_r2 st)
  | Counter2 => Build_FMState (state_ip st) (state_r1 st) v
  end.

(*@inline@[[`write_counter` updates exactly one register while leaving the instruction pointer and the other register unchanged.]]@*)

(*@unicodemath@[[write_counter(Counter1, v, (ip, r1, r2)) = (ip, v, r2)]][[write_counter(Counter2, v, (ip, r1, r2)) = (ip, r1, v).]]@*)

Definition set_ip (ip : nat) (st : FMState) : FMState :=
  Build_FMState ip (state_r1 st) (state_r2 st).

(*@inline@[[`initial_state` loads a one-counter input into `R1` with `IP = 1`, while `initial_state2` exposes the more general two-register starting configuration used in worked machine examples.]]@*)

(*@unicodemath@[[initial_state(input) = (1, input, 0)]][[initial_state2(r1, r2) = (1, r1, r2).]]@*)

Definition initial_state (input : nat) : FMState :=
  Build_FMState 1 input 0.

Definition initial_state2 (r1 r2 : nat) : FMState :=
  Build_FMState 1 r1 r2.

(*@inline@[[`state_well_formed_intro` is the constructor lemma for the machine-side range invariant. It packages the three scalar window bounds into the single state predicate used by the operational semantics.]]@*)

(*@unicodemath@[[ip < ip_limit ∧ r1 < r1_limit ∧ r2 < r2_limit ⇒ state_well_formed(ip, r1, r2).]]@*)

Lemma state_well_formed_intro :
  forall ip r1 r2,
    ip < ip_limit ->
    r1 < r1_limit ->
    r2 < r2_limit ->
    state_well_formed (Build_FMState ip r1 r2).
Proof.
  intros ip r1 r2 Hip Hr1 Hr2.
  split.
  - exact Hip.
  - split.
    + exact Hr1.
    + exact Hr2.
Qed.

(*@inline@[[`initial_ip_bounded` and `zero_below_r2_limit` isolate the two fixed arithmetic facts needed to justify the standard initial configurations.]]@*)

Lemma initial_ip_bounded :
  1 < ip_limit.
Proof.
  unfold ip_limit, K_IP.
  vm_compute.
  lia.
Qed.

Lemma zero_below_r2_limit :
  0 < r2_limit.
Proof.
  unfold r2_limit, K_R2.
  assert (Hpos : fib 65 >= 1) by (apply fib_pos; lia).
  apply Nat.lt_le_trans with (m:=1).
  - apply Nat.lt_0_succ.
  - exact Hpos.
Qed.

Lemma initial_state_well_formed :
  forall input,
    input < r1_limit ->
    state_well_formed (initial_state input).
Proof.
  intros input Hinput.
  unfold initial_state.
  apply state_well_formed_intro.
  - exact initial_ip_bounded.
  - exact Hinput.
  - exact zero_below_r2_limit.
Qed.

Lemma initial_state2_well_formed :
  forall r1 r2,
    r1 < r1_limit ->
    r2 < r2_limit ->
    state_well_formed (initial_state2 r1 r2).
Proof.
  intros r1 r2 Hr1 Hr2.
  unfold initial_state2.
  apply state_well_formed_intro.
  - exact initial_ip_bounded.
  - exact Hr1.
  - exact Hr2.
Qed.

Lemma read_write_same :
  forall c v st,
    read_counter c (write_counter c v st) = v.
Proof.
  intros c v st.
  destruct c; reflexivity.
Qed.

Lemma read_write_other :
  forall c1 c2 v st,
    c1 <> c2 ->
    read_counter c1 (write_counter c2 v st) = read_counter c1 st.
Proof.
  intros c1 c2 v st Hneq.
  destruct c1, c2; try contradiction; reflexivity.
Qed.

Lemma read_set_ip :
  forall c ip st,
    read_counter c (set_ip ip st) = read_counter c st.
Proof.
  intros c ip st.
  destruct c; reflexivity.
Qed.

Lemma state_ip_write_counter :
  forall c v st,
    state_ip (write_counter c v st) = state_ip st.
Proof.
  intros c v st.
  destruct c; reflexivity.
Qed.

(*@inline@[[The preservation lemmas for `write_counter` and `set_ip` isolate the two update modes used by the operational semantics: register writes preserve well-formedness when the new payload is admissible, and IP updates preserve the register bounds automatically.]]@*)

Lemma state_well_formed_write_counter :
  forall st c v,
    state_well_formed st ->
    (match c with
     | Counter1 => v < r1_limit
     | Counter2 => v < r2_limit
     end) ->
    state_well_formed (write_counter c v st).
Proof.
  intros [ip r1 r2] c v [Hip [Hr1 Hr2]] Hv.
  destruct c; simpl in *.
  - apply state_well_formed_intro; assumption.
  - apply state_well_formed_intro; assumption.
Qed.

Lemma state_well_formed_set_ip :
  forall st ip,
    state_well_formed st ->
    ip < ip_limit ->
    state_well_formed (set_ip ip st).
Proof.
  intros [q r1 r2] ip [_ [Hr1 Hr2]] Hip.
  simpl.
  apply state_well_formed_intro; assumption.
Qed.

(*@inline@[[The `_of` well-formedness lemmas lift the machine-definition layer to arbitrary `MachineLimits`. They are the direct parameterized counterparts of the concrete initialization and preservation facts used by the later `Classic_Universality` development.]]@*)

(*@unicodemath@[[input < r1_limit_of(L) ⇒ state_well_formed_of(L, initial_state(input))]][[state_well_formed_of(L, st) ∧ v < r1_limit_of(L) ⇒ state_well_formed_of(L, write_counter(Counter1, v, st))]][[state_well_formed_of(L, st) ∧ v < r2_limit_of(L) ⇒ state_well_formed_of(L, write_counter(Counter2, v, st))]][[state_well_formed_of(L, st) ∧ ip < ip_limit_of(L) ⇒ state_well_formed_of(L, set_ip(ip, st)).]]@*)

Lemma state_well_formed_intro_of :
  forall L ip r1 r2,
    ip < ip_limit_of L ->
    r1 < r1_limit_of L ->
    r2 < r2_limit_of L ->
    state_well_formed_of L (Build_FMState ip r1 r2).
Proof.
  intros L ip r1 r2 Hip Hr1 Hr2.
  split.
  - exact Hip.
  - split.
    + exact Hr1.
    + exact Hr2.
Qed.

Lemma initial_ip_bounded_of :
  forall L,
    1 < ip_limit_of L.
Proof.
  intro L.
  unfold ip_limit_of.
  exact (ml_initial_ip_bounded L).
Qed.

Lemma zero_below_r2_limit_of :
  forall L,
    0 < r2_limit_of L.
Proof.
  intro L.
  unfold r2_limit_of.
  exact (ml_r2_limit_nonzero L).
Qed.

Lemma initial_state_well_formed_of :
  forall L input,
    input < r1_limit_of L ->
    state_well_formed_of L (initial_state input).
Proof.
  intros L input Hinput.
  unfold initial_state.
  apply state_well_formed_intro_of.
  - exact (initial_ip_bounded_of L).
  - exact Hinput.
  - exact (zero_below_r2_limit_of L).
Qed.

Lemma initial_state2_well_formed_of :
  forall L r1 r2,
    r1 < r1_limit_of L ->
    r2 < r2_limit_of L ->
    state_well_formed_of L (initial_state2 r1 r2).
Proof.
  intros L r1 r2 Hr1 Hr2.
  unfold initial_state2.
  apply state_well_formed_intro_of.
  - exact (initial_ip_bounded_of L).
  - exact Hr1.
  - exact Hr2.
Qed.

Lemma state_well_formed_write_counter_of :
  forall L st c v,
    state_well_formed_of L st ->
    (match c with
     | Counter1 => v < r1_limit_of L
     | Counter2 => v < r2_limit_of L
     end) ->
    state_well_formed_of L (write_counter c v st).
Proof.
  intros L [ip r1 r2] c v [Hip [Hr1 Hr2]] Hv.
  destruct c; simpl in *.
  - apply state_well_formed_intro_of; assumption.
  - apply state_well_formed_intro_of; assumption.
Qed.

Lemma state_well_formed_set_ip_of :
  forall L st ip,
    state_well_formed_of L st ->
    ip < ip_limit_of L ->
    state_well_formed_of L (set_ip ip st).
Proof.
  intros L [q r1 r2] ip [_ [Hr1 Hr2]] Hip.
  simpl.
  apply state_well_formed_intro_of; assumption.
Qed.
