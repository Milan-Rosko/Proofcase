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

  This module is a transport boundary, not the internal effectivity proof.
  The normalized checker and its reflection theorems are re-exported from the
  preceding layer; IO commands retain the legacy arithmetic protocol for
  serialized clients and extracted compatibility.

*)

From A002 Require Export A002_02__Normalization.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          ARITHMETIC COMMAND SURFACE                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

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

(*              A002_Verified(d,θ) ≔ A002_Verify_certified(d,θ).              *)

Definition A002_Verified : nat -> nat -> nat :=
  A002_Verify_certified.

(*
│
│          `A002_Certificate_Check` names the executable certificate
│          checker for the IO surface.
│
*)

(*        A002_Certificate_Check(d,θ,p) ≔ A002_Certified_Certb(d,θ,p).        *)

Definition A002_Certificate_Check : nat -> nat -> nat -> bool :=
  A002_Certified_Certb.

(*
│
│          `A002_Parse_Formula` names the formula parser diagnostic
│          for the IO surface.
│
*)

(*            A002_Parse_Formula(φ) ≔ parse_formula_diagnostic(φ).            *)

Definition A002_Parse_Formula : nat -> nat :=
  parse_formula_diagnostic.

(*
│
│          `A002_Parse_Line` names the line parser for the IO surface.
│
*)

(*                    A002_Parse_Line(ℓ) ≔ parse_line(ℓ).                     *)

Definition A002_Parse_Line : nat -> nat :=
  parse_line.

(*
│
│          `A002_IO` dispatches all extraction-facing A002 commands
│          through the certified arithmetic surface.
│
*)

(*   A002_IO(Verify_Query(d,θ))=Verify_Result(A002_Verify_certified(d,θ)).    *)
(*A002_IO(Cert_Check_Query(d,θ,p))=Cert_Check_Result(A002_Certified_Certb(d,θ,p)).*)


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
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            ARITHMETIC DIAGNOSTICS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `Decode_Result` exposes the status and payload of an
│          arithmetic result code through A001 decoding.
│
*)

(*          Decode_Result(encode(status,payload))=(status,payload).           *)

Definition Decode_Result (r : nat) : nat * nat :=
  (result_status r, result_payload r).

(*
│
│          `Decode_Error` exposes an error payload as stage, index,
│          and detail. It is meaningful when the decoded result status
│          is rejection.
│
*)

(*     Decode_Error(code_error(stage,index,detail))=(stage,index,detail).     *)

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

(*       Verify_Diagnostic(d,θ)=(r,result_status(r),result_payload(r))        *)
(*                    where r=A002_Verify_certified(d,θ).                     *)

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

  The compact view changes presentation only: natural-number payloads are
  converted to binary integers after the underlying arithmetic command has
  run. It does not alter validation, normalization, status conventions, or
  error selection.

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

(*                      A002_IO_Z(q)=Z-view(A002_IO(q)).                      *)

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
