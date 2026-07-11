(*A002_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / A002_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Artifact layer for A002. We record assumption reports for the arithmetic
  compatibility facts and the normalized reflection theorems, then extract
  both the legacy arithmetic verifier and the inductive normalized checker to
  OCaml.

  The two normalized reports are the principal logical audit targets:
  `normalized_stepb_iff` relates local computation to K/S/MP validity, and
  `normalized_linesb_iff` lifts that equivalence to derivation lists. The
  remaining reports certify arithmetic result agreement and accepted-result
  shape.

  Extraction erases proofs while retaining the normalized syntax datatypes
  and Boolean checker. `A002_Verifier` contains constructors, parsers,
  arithmetic compatibility functions, and normalized checking; `A002_IO`
  contains the command dispatcher and diagnostic views.

*)

From A002 Require Import A002_95_API.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatBigInt.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              ASSUMPTION REPORTS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The following redirects make the global-context dependency
│          status of each published theorem a reproducible text
│          artifact.
│
*)

Redirect "theories/A002/_appendix/_assumptions/verify_accept_sound"
  Print Assumptions verify_accept_sound.

Redirect "theories/A002/_appendix/_assumptions/generated_cert_checks"
  Print Assumptions generated_cert_checks.

Redirect "theories/A002/_appendix/_assumptions/check_axk_sound"
  Print Assumptions check_axk_sound.

Redirect "theories/A002/_appendix/_assumptions/check_axs_sound"
  Print Assumptions check_axs_sound.

Redirect "theories/A002/_appendix/_assumptions/check_mp_sound"
  Print Assumptions check_mp_sound.

Redirect "theories/A002/_appendix/_assumptions/normalized_stepb_iff"
  Print Assumptions normalized_stepb_iff.

Redirect "theories/A002/_appendix/_assumptions/normalized_linesb_iff"
  Print Assumptions normalized_linesb_iff.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               OCAML EXTRACTION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          IO aliases are inlined so the extracted entry points reduce
│          directly to their verifier, certificate, and parser
│          implementations. Natural numbers are mapped to
│          arbitrary-precision OCaml integers.
│
*)

Extraction Inline A002_Verified A002_Certificate_Check.
Extraction Inline A002_Parse_Formula A002_Parse_Line.
Extraction Language OCaml.

Extraction "theories/A002/_appendix/_artifacts/A002_Verifier"
  A002_Verify A002_Certb
  NormalizedFormula NormalizedRule NormalizedLine
  normalized_formula_eqb normalized_stepb normalized_linesb
  code_var code_imp code_line tag_axk tag_axs tag_mp code_derivation
  parse_imp parse_line
  check_axk check_axs check_mp.

Extraction "theories/A002/_appendix/_artifacts/A002_IO"
  A002_IO A002_IO_Z
  A002_Verified A002_Certificate_Check
  A002_Parse_Formula A002_Parse_Line
  Decode_Result Decode_Error
  Verify_Diagnostic Verify_Diagnostic_Z.
