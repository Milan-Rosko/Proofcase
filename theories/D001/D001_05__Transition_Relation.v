(*D001_05__Transition_Relation.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                   Proofcase / D001_05__Transition_Relation                   │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file defines the one-step execution kernel of the Fibonacci Machine.
  Externally, a machine state is represented by a single natural number `s`,
  and `NextState` is obtained by decoding `s`, executing one Minsky step, and
  re-encoding the result.

*)

From D001 Require Export D001_04__Machine_Definition.

Definition fetch_instruction (prog : program) (st : FMState) : option instruction :=
  nth_error prog (state_ip st).

Definition halted_state (st : FMState) : Prop :=
  state_ip st = 0.

(*
│
│          `step_state` is the internal one-step execution kernel on
│          structured machine states. It performs a single ROM fetch
│          and then applies the corresponding Minsky update.
│
*)

Definition step_state (prog : program) (st : FMState) : FMState :=
  match state_ip st with
  | 0 => st
  | _ =>
      match fetch_instruction prog st with
      | Some (INC c next_ip) =>
          set_ip next_ip (write_counter c (S (read_counter c st)) st)
      | Some (JZDEC c zero_ip dec_ip) =>
          if Nat.eqb (read_counter c st) 0
          then set_ip zero_ip st
          else set_ip dec_ip (write_counter c (Nat.pred (read_counter c st)) st)
      | Some HALT => set_ip 0 st
      | None => set_ip 0 st
      end
  end.

(*      step_state_relation(prog, st, st') ⇔ st' = step_state(prog, st).      *)

Definition step_state_relation (prog : program) (st st' : FMState) : Prop :=
  st' = step_state prog st.

(*
│
│          `NextState` is the external transition on numeric state
│          codes: decode the raw code through the total codec
│          projection, execute one structured step, and then
│          re-encode. On arbitrary naturals, the machine therefore
│          first collapses to the canonical bounded state image before
│          stepping.
│
*)

Definition NextState (prog : program) (s : nat) : nat :=
  encode_state (step_state prog (decode_state s)).

Definition step_code : program -> nat -> nat := NextState.

Definition step_relation (prog : program) (s t : nat) : Prop :=
  t = NextState prog s.

Definition stepb (prog : program) (s t : nat) : bool :=
  Nat.eqb (NextState prog s) t.

(*
│
│          `stepb` is the boolean recognizer for the single-step graph
│          on encoded states. It packages the total transition
│          function as a decidable edge test.
│
*)

(*
│
│          `step_state_relation_step` and `step_relation_next` are the
│          canonical witnesses for the structured and encoded
│          transition graphs. They package the defining equalities
│          that later existential and determinism proofs appeal to.
│
*)

Lemma step_state_relation_step :
  forall prog st,
    step_state_relation prog st (step_state prog st).
Proof.
  intros prog st.
  reflexivity.
Qed.

Lemma step_relation_next :
  forall prog s,
    step_relation prog s (NextState prog s).
Proof.
  intros prog s.
  reflexivity.
Qed.

(*        state_well_formed(st) ⇒ NextState(prog, encode_state(st)) =         *)
(*                    encode_state(step_state(prog, st)).                     *)

Theorem NextState_on_encoded_state :
  forall prog st,
    state_well_formed st ->
    NextState prog (encode_state st) = encode_state (step_state prog st).
Proof.
  intros prog st Hwf.
  unfold NextState.
  rewrite decode_state_encode_state by exact Hwf.
  reflexivity.
Qed.

(*           stepb(prog, s, t) = true ⇔ step_relation(prog, s, t).            *)

Theorem stepb_correct :
  forall prog s t,
    stepb prog s t = true <-> step_relation prog s t.
Proof.
  intros prog s t.
  unfold stepb, step_relation.
  rewrite Nat.eqb_eq.
  split; intro H; symmetry; exact H.
Qed.

Theorem step_total :
  forall prog s,
    exists t, step_relation prog s t.
Proof.
  intros prog s.
  exists (NextState prog s).
  apply step_relation_next.
Qed.

Lemma halted_state_fixed :
  forall prog st,
    halted_state st ->
    step_state prog st = st.
Proof.
  intros prog st Hhalt.
  unfold halted_state in Hhalt.
  destruct st as [ip r1 r2].
  simpl in *.
  subst ip.
  reflexivity.
Qed.

Corollary step_state_deterministic :
  forall prog st st1 st2,
    step_state_relation prog st st1 ->
    step_state_relation prog st st2 ->
    st1 = st2.
Proof.
  intros prog st st1 st2 H1 H2.
  unfold step_state_relation in *.
  congruence.
Qed.

(*
│
│          `NextState_of` is the corresponding projected external step
│          relative to an arbitrary limit package `L`: total decode
│          into the bounded image for `L`, one structured transition,
│          and then re-encode.
│
*)

Definition NextState_of (L : MachineLimits) (prog : program) (s : nat) : nat :=
  encode_state_of L (step_state prog (decode_state_of L s)).

Definition step_code_of (L : MachineLimits) : program -> nat -> nat :=
  NextState_of L.

Definition step_relation_of (L : MachineLimits) (prog : program) (s t : nat) : Prop :=
  t = NextState_of L prog s.

Definition stepb_of (L : MachineLimits) (prog : program) (s t : nat) : bool :=
  Nat.eqb (NextState_of L prog s) t.

(*
│
│          The `_of` transition API lifts the external numeric step
│          relation to an arbitrary `MachineLimits` package. The
│          underlying structured machine step is unchanged; only the
│          surrounding state codec becomes parameterized.
│
*)

(*       NextState_of(L, prog, s) = encode_state_of(L, step_state(prog,       *)
(*                          decode_state_of(L, s))).                          *)

(*
│
│          `NextState_on_encoded_state_of`, `stepb_correct_of`, and
│          `step_total_of` are the generic external-dynamics facts for
│          the parameterized family. They are the exact analogues of
│          the concrete encoded-step theorems, now prepared for later
│          statements quantified over `MachineLimits`.
│
*)

(*state_well_formed_of(L, st) ⇒ NextState_of(L, prog, encode_state_of(L, st)) *)
(*                 = encode_state_of(L, step_state(prog, st))                 *)
(*      stepb_of(L, prog, s, t) = true ⇔ step_relation_of(L, prog, s, t)      *)
(*                 ∀ s, ∃ t, step_relation_of(L, prog, s, t).                 *)

Theorem NextState_on_encoded_state_of :
  forall L prog st,
    state_well_formed_of L st ->
    NextState_of L prog (encode_state_of L st) =
    encode_state_of L (step_state prog st).
Proof.
  intros L prog st Hwf.
  unfold NextState_of.
  rewrite decode_state_encode_state_of by exact Hwf.
  reflexivity.
Qed.

Theorem stepb_correct_of :
  forall L prog s t,
    stepb_of L prog s t = true <-> step_relation_of L prog s t.
Proof.
  intros L prog s t.
  unfold stepb_of, step_relation_of.
  rewrite Nat.eqb_eq.
  split; intro H; symmetry; exact H.
Qed.

Theorem step_total_of :
  forall L prog s,
    exists t, step_relation_of L prog s t.
Proof.
  intros L prog s.
  exists (NextState_of L prog s).
  reflexivity.
Qed.
