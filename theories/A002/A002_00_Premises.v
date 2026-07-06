(*A002_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / A002_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Premise layer for A002/EFFECTIVE ARITHMETIC CERTIFICATE VERIFIER. We fix
  the shared standard-library and A001 pairing environment, then name the
  status conventions, result constructors, error stages, and error details
  used by the executable verifier layers.

  The verifier surface of A002 is deliberately arithmetic: every exported
  checking result is a natural number, read through the certified A001
  pairing function as a status/payload pair. This file contains only neutral
  vocabulary and no proof-search or semantic-verification machinery.

*)

From Stdlib Require Export Arith PeanoNat Bool Lia List Ring ZArith Extraction.
From A001 Require Export A001_95_API.
Export ListNotations.
Global Open Scope list_scope.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        ARITHMETIC RESULT CONVENTIONS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A002 returns A001-coded status/payload pairs. Status `0`
│          means rejection and status `1` means acceptance.
│
*)

Definition STATUS_REJECT : nat := 0.
Definition STATUS_ACCEPT : nat := 1.

(*
│
│          `accept payload` packages a successful arithmetic result.
│          The payload is always an explicit natural-number
│          certificate or local certificate component.
│
*)

Definition accept (payload : nat) : nat :=
  encode STATUS_ACCEPT payload.

(*
│
│          `code_error stage index detail` records the first local
│          failure seen by a checker. The stage identifies the
│          verifier layer, the index identifies the global or
│          line-local position, and the detail identifies the concrete
│          failure.
│
*)

Definition code_error (stage index detail : nat) : nat :=
  encode stage (encode index detail).

(*
│
│          `reject` packages an arithmetic failure result. No
│          rejection branch returns an uncoded diagnostic.
│
*)

Definition reject (stage index detail : nat) : nat :=
  encode STATUS_REJECT (code_error stage index detail).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 ERROR STAGES                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The stage constants partition errors by verifier layer.
│          Global errors use index `0`; line-local errors use the
│          current line index.
│
*)

Definition STAGE_DERIVATION_HEADER : nat := 0.
Definition STAGE_LIST_STRUCTURE : nat := 1.
Definition STAGE_LINE : nat := 2.
Definition STAGE_TAG : nat := 3.
Definition STAGE_FORMULA : nat := 4.
Definition STAGE_RULE : nat := 5.
Definition STAGE_CONCLUSION : nat := 6.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             COMMON ERROR DETAILS                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Common structural errors are shared by parsers, list
│          destructors, and the main verifier.
│
*)

Definition ERR_NONCANONICAL_DERIVATION : nat := 0.
Definition ERR_BAD_DERIVATION_LENGTH : nat := 1.
Definition ERR_EMPTY_DERIVATION : nat := 2.
Definition ERR_BAD_CONCLUSION : nat := 3.
Definition ERR_FUEL_EXHAUSTED : nat := 4.
Definition ERR_NONCANONICAL_NODE : nat := 5.
Definition ERR_BAD_TAG : nat := 6.
Definition ERR_BAD_LIST_TAG : nat := 7.
Definition ERR_EXPECTED_CONS : nat := 8.
Definition ERR_EXPECTED_NIL : nat := 9.
Definition ERR_INDEX_OUT_OF_RANGE : nat := 10.
Definition ERR_NONCANONICAL_LINE : nat := 11.
Definition ERR_BAD_LINE_FORMULA : nat := 12.
Definition ERR_UNKNOWN_RULE : nat := 13.

(*
│
│          Formula-parser errors distinguish non-canonical inputs,
│          non-implication nodes, and malformed implication payloads.
│
*)

Definition ERR_NONCANONICAL_FORMULA : nat := 20.
Definition ERR_BAD_FORMULA_TAG : nat := 21.
Definition ERR_BAD_VAR_PAYLOAD : nat := 22.
Definition ERR_BAD_IMP_PAYLOAD : nat := 23.
Definition ERR_NOT_IMP : nat := 24.

(*
│
│          K-axiom errors identify the first failed syntactic
│          obligation in the shape `A -> (B -> A)`.
│
*)

Definition ERR_AXK_NOT_IMP_1 : nat := 40.
Definition ERR_AXK_NOT_IMP_2 : nat := 41.
Definition ERR_AXK_A_MISMATCH : nat := 42.
Definition ERR_AXK_BAD_A : nat := 43.
Definition ERR_AXK_BAD_B : nat := 44.

(*
│
│          S-axiom errors identify the first failed syntactic
│          obligation in the shape `(A -> (B -> C)) -> ((A -> B) -> (A
│          -> C))`.
│
*)

Definition ERR_AXS_NOT_IMP_1 : nat := 60.
Definition ERR_AXS_NOT_IMP_2 : nat := 61.
Definition ERR_AXS_NOT_IMP_3 : nat := 62.
Definition ERR_AXS_NOT_IMP_4 : nat := 63.
Definition ERR_AXS_NOT_IMP_5 : nat := 64.
Definition ERR_AXS_NOT_IMP_6 : nat := 65.
Definition ERR_AXS_A_MISMATCH_LEFT : nat := 66.
Definition ERR_AXS_A_MISMATCH_RIGHT : nat := 67.
Definition ERR_AXS_B_MISMATCH : nat := 68.
Definition ERR_AXS_C_MISMATCH : nat := 69.
Definition ERR_AXS_BAD_A : nat := 70.
Definition ERR_AXS_BAD_B : nat := 71.
Definition ERR_AXS_BAD_C : nat := 72.

(*
│
│          Modus-ponens errors identify malformed citations, malformed
│          cited lines, and mismatch against the cited implication.
│
*)

Definition ERR_MP_BAD_P : nat := 90.
Definition ERR_MP_BAD_Q : nat := 91.
Definition ERR_MP_P_NOT_LT_J : nat := 92.
Definition ERR_MP_Q_NOT_LT_J : nat := 93.
Definition ERR_MP_BAD_LINE_J : nat := 94.
Definition ERR_MP_BAD_LINE_P : nat := 95.
Definition ERR_MP_BAD_LINE_Q : nat := 96.
Definition ERR_MP_Q_NOT_IMP : nat := 97.
Definition ERR_MP_ANTECEDENT_MISMATCH : nat := 98.
Definition ERR_MP_CONSEQUENT_MISMATCH : nat := 99.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              PUBLIC SHAPE TYPES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The exported verifier consumes a derivation code and a
│          target formula code, and returns an A001-coded arithmetic
│          result.
│
*)

Definition verifier_t : Type := nat -> nat -> nat.

(*
│
│          The standalone certificate checker consumes a derivation
│          code, a target formula code, and a certificate payload, and
│          returns an executable Boolean.
│
*)

Definition cert_checker_t : Type := nat -> nat -> nat -> bool.
