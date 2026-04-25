(*D001_99_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / D001_99_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Driver file for D001 artifact generation: terminal assumption reports for
  the public Iterant bridge theorems and OCaml extraction of the executable
  machine surfaces. Isolated here so `D001_98_API` remains import-safe for
  proof-facing clients.

*)

(*
│
│          The artifact driver imports the public API and the OCaml
│          extraction back ends.
│
*)

From D001 Require Import D001_98_API.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatBigInt.

(*
│
│          The pairing assumption report records the dependencies of
│          the machine-local carryless pairing roundtrip theorem.
│
*)

Redirect "theories/D001/_appendix/_assumptions/Iterant_pair_roundtrip"
  Print Assumptions Iterant_pair_roundtrip.

(*
│
│          The pairing injectivity assumption report records the
│          dependencies of the machine-local carryless pairing
│          uniqueness theorem.
│
*)

Redirect "theories/D001/_appendix/_assumptions/Iterant_pair_injective"
  Print Assumptions Iterant_pair_injective.

(*
│
│          The codec assumption report records the dependencies of the
│          state decode-after-encode theorem.
│
*)

Redirect "theories/D001/_appendix/_assumptions/decode_state_encode_state"
  Print Assumptions decode_state_encode_state.

(*
│
│          The additive-step assumption report records the
│          dependencies of the encoded one-step arithmetic law.
│
*)

Redirect "theories/D001/_appendix/_assumptions/NextState_additive"
  Print Assumptions NextState_additive.

(*
│
│          The run-bridge assumption report records the dependencies
│          of the abstract-to-structured run equivalence.
│
*)

Redirect "theories/D001/_appendix/_assumptions/abstract_run_steps_state_bridge"
  Print Assumptions abstract_run_steps_state_bridge.

(*
│
│          The acceptance-bridge assumption report records the
│          dependencies of the family-to-classical acceptance theorem.
│
*)

Redirect "theories/D001/_appendix/_assumptions/FamilyMachineAccepts_implies_Classic"
  Print Assumptions FamilyMachineAccepts_implies_Classic.

Extraction Inline Iterant_Z0 Iterant_encode_pair Iterant_decode_pair step_code.

Extraction Language OCaml.

(*
│
│          The Vector Iterant artifact extracts the executable codec,
│          transition, trace, run, and worked-program surfaces.
│
*)

Extraction "D001_Vector_Iterant"
  encode_state
  decode_state
  normalize_state_code
  read_counter
  write_counter
  set_ip
  initial_state
  initial_state2
  fetch_instruction
  step_state
  NextState
  stepb
  encode_nat_list
  coded_nth
  code_run_last
  code_run_trace
  run_steps
  abstract_initial_config
  abstract_next
  abstract_run_steps
  subtraction_program.
