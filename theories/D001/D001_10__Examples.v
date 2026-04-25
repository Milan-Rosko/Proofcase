(*D001_10__Examples.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / D001_10__Examples                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file is a lightweight example layer over the completed D001
  development.

  Each example is a direct specialization of an already-proved theorem, so
  the file stays fast to compile and easy to audit.

*)

From D001 Require Export D001_98_API.

(*
│
│          `zero_lt_r1_limit` is the tiny arithmetic side lemma needed
│          to instantiate the generic initial-state well-formedness
│          theorem at input `0`.
│
*)

Lemma zero_lt_r1_limit :
  0 < r1_limit.
Proof.
  unfold r1_limit, K_R1.
  pose proof (fib_pos 53 ltac:(lia)) as Hfib.
  lia.
Qed.

(*
│
│          The examples cover five concrete checkpoints: codec
│          roundtrip, one-step machine behavior, a finite subtraction
│          run, classical abstract acceptance, and the bridges from
│          family acceptance to raw-witness and classical semantics.
│
*)
(*      decode_state(encode_state(initial_state(0))) = initial_state(0)       *)
(*    run_steps(subtraction_program, 5, initial_state2(3, 2)) = (0, 1, 0)     *)
(*           FamilyMachineAccepts(subtraction_program, 3) ⇒ ∃ L, w,           *)
(*            FamilyRawTraceWitness(L, subtraction_program, 3, w).            *)

Example initial_state_0_codec_roundtrip :
  decode_state (encode_state (initial_state 0)) = initial_state 0.
Proof.
  apply decode_state_encode_state.
  apply initial_state_well_formed.
  exact zero_lt_r1_limit.
Qed.

Example subtraction_step_halt_3 :
  step_state subtraction_program (Build_IterantState 1 3 0) =
  Build_IterantState 0 3 0.
Proof.
  exact (subtraction_halt_step 3).
Qed.

Example subtraction_run_3_2 :
  run_steps subtraction_program 5 (initial_state2 3 2) =
  Build_IterantState 0 1 0.
Proof.
  replace 5 with (S (2 * 2)) by lia.
  apply subtraction_program_halts.
  lia.
Qed.

Example subtraction_classic_accepts_3_2 :
  abstract_halted
    (abstract_run_steps subtraction_program (S (2 * 2)) (1, 3, 2)).
Proof.
  apply subtraction_program_classic_accepts.
  lia.
Qed.

Example subtraction_family_raw_witness_bridge_3 :
  FamilyMachineAccepts subtraction_program 3 ->
  exists L witness,
    FamilyRawTraceWitness L subtraction_program 3 witness.
Proof.
  intro Hacc.
  exact (FamilyMachineAccepts_has_raw_witness subtraction_program 3 Hacc).
Qed.

Example subtraction_family_to_classic_bridge_3 :
  FamilyMachineAccepts subtraction_program 3 ->
  ClassicMachineAccepts subtraction_program 3.
Proof.
  exact (FamilyMachineAccepts_implies_Classic subtraction_program 3).
Qed.
