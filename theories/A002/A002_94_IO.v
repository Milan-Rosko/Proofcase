(*A002_94_IO.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                            Proofcase / A002_94_IO                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Extraction-facing IO surface for A002. We provide commands for running the
  verifier, checking a certificate payload, parsing a formula diagnostic, and
  parsing a proof line.

  The IO surface remains arithmetic: verification and parser commands return
  natural-number result codes, while certificate checking returns an
  executable Boolean. Compact `*_Z` views mirror the same commands with
  binary-integer numeric payloads for readable computation.

*)

From A002 Require Export A002_08__Soundness.

(*
│
│          The executable query type exposes verification, certificate
│          checking, formula parsing, and line parsing.
│
*)

Inductive A002_IO_Query : Type :=
| Verify_Query : nat -> nat -> A002_IO_Query
| Cert_Check_Query : nat -> nat -> nat -> A002_IO_Query
| Parse_Formula_Query : nat -> A002_IO_Query
| Parse_Line_Query : nat -> A002_IO_Query.

(*
│
│          The executable result type returns either an arithmetic
│          result code, a Boolean certificate-check result, or a
│          parser result code.
│
*)

Inductive A002_IO_Result : Type :=
| Verify_Result : nat -> A002_IO_Result
| Cert_Check_Result : bool -> A002_IO_Result
| Parse_Result : nat -> A002_IO_Result.

(*
│
│          `A002_Verified` names the verifier for the IO surface.
│
*)

Definition A002_Verified : nat -> nat -> nat :=
  A002_Verify.

(*
│
│          `A002_Certificate_Check` names the executable certificate
│          checker for the IO surface.
│
*)

Definition A002_Certificate_Check : nat -> nat -> nat -> bool :=
  A002_Certb.

(*
│
│          `A002_Parse_Formula` names the formula parser diagnostic
│          for the IO surface.
│
*)

Definition A002_Parse_Formula : nat -> nat :=
  parse_formula_diagnostic.

(*
│
│          `A002_Parse_Line` names the line parser for the IO surface.
│
*)

Definition A002_Parse_Line : nat -> nat :=
  parse_line.

(*
│
│          `A002_IO` dispatches all extraction-facing A002 commands
│          through the certified arithmetic surface.
│
*)

Definition A002_IO (q : A002_IO_Query) : A002_IO_Result :=
  match q with
  | Verify_Query d theta =>
      Verify_Result (A002_Verified d theta)
  | Cert_Check_Query d theta p =>
      Cert_Check_Result (A002_Certificate_Check d theta p)
  | Parse_Formula_Query phi =>
      Parse_Result (A002_Parse_Formula phi)
  | Parse_Line_Query ell =>
      Parse_Result (A002_Parse_Line ell)
  end.

(*
│
│          `Decode_Result` exposes the status and payload of an
│          arithmetic result code through A001 decoding.
│
*)

Definition Decode_Result (r : nat) : nat * nat :=
  (result_status r, result_payload r).

(*
│
│          `Decode_Error` exposes an error payload as stage, index,
│          and detail. It is meaningful when the decoded result status
│          is rejection.
│
*)

Definition Decode_Error (payload : nat) : nat * nat * nat :=
  let stage := fst001 payload in
  let index_detail := snd001 payload in
  (stage, fst001 index_detail, snd001 index_detail).

(*
│
│          `Verify_Diagnostic` returns the raw verifier result
│          together with its decoded status and payload.
│
*)

Definition Verify_Diagnostic (d theta : nat) : nat * nat * nat :=
  let r := A002_Verified d theta in
  (r, result_status r, result_payload r).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             COMPACT INTEGER VIEW                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `A002_Verified_Z` returns the raw verifier result as a
│          binary integer.
│
*)

Definition A002_Verified_Z (d theta : nat) : BinNums.Z :=
  Z.of_nat (A002_Verified d theta).

(*
│
│          `A002_Parse_Formula_Z` returns the formula diagnostic
│          result as a binary integer.
│
*)

Definition A002_Parse_Formula_Z (phi : nat) : BinNums.Z :=
  Z.of_nat (A002_Parse_Formula phi).

(*
│
│          `A002_Parse_Line_Z` returns the line parser result as a
│          binary integer.
│
*)

Definition A002_Parse_Line_Z (ell : nat) : BinNums.Z :=
  Z.of_nat (A002_Parse_Line ell).

(*
│
│          `Decode_Result_Z` exposes a result code as binary-integer
│          status and payload.
│
*)

Definition Decode_Result_Z (r : nat) : BinNums.Z * BinNums.Z :=
  (Z.of_nat (result_status r), Z.of_nat (result_payload r)).

(*
│
│          `Decode_Error_Z` exposes an error payload as binary-integer
│          stage, index, and detail.
│
*)

Definition Decode_Error_Z (payload : nat) : BinNums.Z * BinNums.Z * BinNums.Z :=
  let decoded := Decode_Error payload in
  match decoded with
  | (stage, index, detail) =>
      (Z.of_nat stage, Z.of_nat index, Z.of_nat detail)
  end.

(*
│
│          The compact result type mirrors `A002_IO_Result`, but
│          stores numeric payloads as binary integers.
│
*)

Inductive A002_IO_Result_Z : Type :=
| Verify_Result_Z : BinNums.Z -> A002_IO_Result_Z
| Cert_Check_Result_Z : bool -> A002_IO_Result_Z
| Parse_Result_Z : BinNums.Z -> A002_IO_Result_Z.

(*
│
│          `A002_IO_Z` dispatches the compact integer view of the
│          executable interface.
│
*)

Definition A002_IO_Z (q : A002_IO_Query) : A002_IO_Result_Z :=
  match q with
  | Verify_Query d theta =>
      Verify_Result_Z (A002_Verified_Z d theta)
  | Cert_Check_Query d theta p =>
      Cert_Check_Result_Z (A002_Certificate_Check d theta p)
  | Parse_Formula_Query phi =>
      Parse_Result_Z (A002_Parse_Formula_Z phi)
  | Parse_Line_Query ell =>
      Parse_Result_Z (A002_Parse_Line_Z ell)
  end.

(*
│
│          The compact verifier diagnostic returns the raw result code
│          and decoded status/payload as binary integers.
│
*)

Definition Verify_Diagnostic_Z
  (d theta : nat)
  : BinNums.Z * BinNums.Z * BinNums.Z :=
  let diag := Verify_Diagnostic d theta in
  match diag with
  | (raw, status, payload) =>
      (Z.of_nat raw, Z.of_nat status, Z.of_nat payload)
  end.
