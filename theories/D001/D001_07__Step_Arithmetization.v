(*D001_07__Step_Arithmetization.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / D001_07__Step_Arithmetization                   │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file isolates the boolean observation predicates and additive delta
  formulas that describe a single encoded FM step.

  Its main result is an additive step law: at the integer level, the
  successor code is the source code plus the instruction-pointer contribution
  and the combined register contribution.

*)

From D001 Require Export D001_06__Trace_Witness.

(*
│
│          `source_state` and `target_state` are naming conveniences
│          for the decoded predecessor and successor codes appearing
│          throughout the boolean observation layer.
│
*)

Definition source_state (s : nat) : FMState := decode_state s.

Definition target_state (t : nat) : FMState := decode_state t.

(*
│
│          The boolean atoms in this file are observation predicates
│          on decoded states. They separate control-flow tests from
│          additive delta formulas, so later encodings can refer to
│          one FM step without reopening the operational semantics
│          each time.
│
*)

Definition ip_eqb (q : nat) (s : nat) : bool :=
  Nat.eqb (state_ip (source_state s)) q.

Definition counter_zero_b (c : counter) (s : nat) : bool :=
  Nat.eqb (read_counter c (source_state s)) 0.

Definition target_ipb (q : nat) (t : nat) : bool :=
  Nat.eqb (state_ip (target_state t)) q.

Definition counter_succ_b (c : counter) (s t : nat) : bool :=
  let st_s := source_state s in
  let st_t := target_state t in
  Nat.eqb
    (read_counter c st_t)
    (S (read_counter c st_s)).

Definition counter_pred_b (c : counter) (s t : nat) : bool :=
  let st_s := source_state s in
  let st_t := target_state t in
  Nat.eqb
    (read_counter c st_s)
    (S (read_counter c st_t)).

Definition frozen_other_counter_b (c : counter) (s t : nat) : bool :=
  let st_s := source_state s in
  let st_t := target_state t in
  match c with
  | Counter1 => Nat.eqb (state_r2 st_s) (state_r2 st_t)
  | Counter2 => Nat.eqb (state_r1 st_s) (state_r1 st_t)
  end.

(*
│
│          `ip_delta`, `r1_delta`, and `r2_delta` measure the additive
│          effect of replacing one band payload by another at the
│          level of encoded natural numbers.
│
*)
(*              ip_delta(q, q') = Z(ip_code(q')) - Z(ip_code(q))              *)
(*              r1_delta(v, v') = Z(r1_code(v')) - Z(r1_code(v))              *)
(*             r2_delta(v, v') = Z(r2_code(v')) - Z(r2_code(v))].             *)

Definition ip_delta (q q' : nat) : BinNums.Z :=
  (Z.of_nat (ip_code q') - Z.of_nat (ip_code q))%Z.

Definition r1_delta (v v' : nat) : BinNums.Z :=
  (Z.of_nat (r1_code v') - Z.of_nat (r1_code v))%Z.

Definition r2_delta (v v' : nat) : BinNums.Z :=
  (Z.of_nat (r2_code v') - Z.of_nat (r2_code v))%Z.

Definition step_ip_delta (prog : program) (st : FMState) : BinNums.Z :=
  ip_delta (state_ip st) (state_ip (step_state prog st)).

Definition step_register_delta (prog : program) (st : FMState) : BinNums.Z :=
  (r1_delta (state_r1 st) (state_r1 (step_state prog st)) +
   r2_delta (state_r2 st) (state_r2 (step_state prog st)))%Z.

Lemma source_state_eq :
  forall s, source_state s = decode_state s.
Proof.
  reflexivity.
Qed.

Lemma target_state_eq :
  forall t, target_state t = decode_state t.
Proof.
  reflexivity.
Qed.

(*
│
│          `next_state_delta_split` is the definitional expansion
│          point for the two aggregate deltas attached to one machine
│          step. It keeps the main additive theorem from reopening
│          those definitions inline.
│
*)

Lemma next_state_delta_split :
  forall prog st,
    step_ip_delta prog st = ip_delta (state_ip st) (state_ip (step_state prog st)) /\
    step_register_delta prog st =
    (r1_delta (state_r1 st) (state_r1 (step_state prog st)) +
     r2_delta (state_r2 st) (state_r2 (step_state prog st)))%Z.
Proof.
  intros prog st.
  split; reflexivity.
Qed.

Lemma ip_eqb_correct :
  forall q s,
    ip_eqb q s = true <-> state_ip (decode_state s) = q.
Proof.
  intros q s.
  unfold ip_eqb.
  rewrite source_state_eq.
  rewrite Nat.eqb_eq.
  split; intro H; lia.
Qed.

Lemma counter_zero_b_correct :
  forall c s,
    counter_zero_b c s = true <-> read_counter c (decode_state s) = 0.
Proof.
  intros c s.
  unfold counter_zero_b.
  rewrite source_state_eq.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

Lemma target_ipb_correct :
  forall q t,
    target_ipb q t = true <-> state_ip (decode_state t) = q.
Proof.
  intros q t.
  unfold target_ipb.
  rewrite target_state_eq.
  rewrite Nat.eqb_eq.
  split; intro H; lia.
Qed.

Lemma counter_succ_b_correct :
  forall c s t,
    counter_succ_b c s t = true <->
    read_counter c (decode_state t) =
    S (read_counter c (decode_state s)).
Proof.
  intros c s t.
  unfold counter_succ_b.
  cbn.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

Lemma counter_pred_b_correct :
  forall c s t,
    counter_pred_b c s t = true <->
    read_counter c (decode_state s) =
    S (read_counter c (decode_state t)).
Proof.
  intros c s t.
  unfold counter_pred_b.
  cbn.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

Lemma frozen_other_counter_b_correct :
  forall c s t,
    frozen_other_counter_b c s t = true <->
    match c with
    | Counter1 => state_r2 (decode_state s) = state_r2 (decode_state t)
    | Counter2 => state_r1 (decode_state s) = state_r1 (decode_state t)
    end.
Proof.
  intros c s t.
  destruct c; unfold frozen_other_counter_b; cbn; rewrite Nat.eqb_eq; tauto.
Qed.

Lemma encode_state_additive :
  forall st st',
    Z.of_nat (encode_state st') =
    (Z.of_nat (encode_state st) +
     ip_delta (state_ip st) (state_ip st') +
     r1_delta (state_r1 st) (state_r1 st') +
     r2_delta (state_r2 st) (state_r2 st'))%Z.
Proof.
  intros st st'.
  rewrite !encode_state_as_components.
  unfold ip_delta, r1_delta, r2_delta.
  lia.
Qed.

(*
│
│          `NextState_additive` is the core arithmetization theorem:
│          one machine step changes the encoded state by an
│          instruction-pointer contribution plus the combined register
│          contribution.
│
*)
(*       state_well_formed(st) ⇒ Z(NextState(prog, encode_state(st))) =       *)
(* Z(encode_state(st)) + step_ip_delta(prog, st) + step_register_delta(prog,  *)
(*                                    st).                                    *)

Theorem NextState_additive :
  forall prog st,
    state_well_formed st ->
    Z.of_nat (NextState prog (encode_state st)) =
    (Z.of_nat (encode_state st) +
     step_ip_delta prog st +
     step_register_delta prog st)%Z.
Proof.
  intros prog st Hwf.
  rewrite NextState_on_encoded_state by exact Hwf.
  destruct (next_state_delta_split prog st) as [Hipdelta Hregdelta].
  rewrite Hipdelta, Hregdelta.
  rewrite encode_state_additive with (st:=st) (st':=step_state prog st).
  lia.
Qed.

(*
│
│          `HALT_additive` specializes the additive step law to
│          halting instructions: the register delta vanishes, so only
│          the instruction-pointer jump to `0` remains.
│
*)
(*     state_well_formed(st) ∧ fetch_instruction(prog, st) = Some HALT ⇒      *)
(*        Z(NextState(prog, encode_state(st))) = Z(encode_state(st)) +        *)
(*                         ip_delta(state_ip(st), 0).                         *)

Corollary HALT_additive :
  forall prog st,
    state_well_formed st ->
    fetch_instruction prog st = Some HALT ->
    Z.of_nat (NextState prog (encode_state st)) =
    (Z.of_nat (encode_state st) + ip_delta (state_ip st) 0)%Z.
Proof.
  intros prog st Hwf Hhalt.
  rewrite NextState_additive by exact Hwf.
  unfold step_ip_delta, step_register_delta.
  unfold step_state.
  destruct (state_ip st) eqn:Hip.
  - rewrite Hip.
    unfold r1_delta, r2_delta, ip_delta.
    simpl.
    lia.
  - rewrite Hhalt.
    unfold r1_delta, r2_delta, ip_delta.
    simpl.
    lia.
Qed.
