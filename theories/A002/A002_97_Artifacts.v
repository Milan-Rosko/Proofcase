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

  Artifact layer for A002/CARRYLESS SEQUENT. We record assumption reports for
  arithmetic compatibility, normalized reflection, target-sensitive
  verification, and end-to-end certified arithmetic acceptance, then extract
  the legacy and certified verifier surfaces to OCaml.

  The principal audit chain is `normalized_stepb_iff`,
  `normalized_linesb_iff`, `normalized_failure_index_none_iff`,
  `normalized_verifyb_iff`, `certified_verify_accept_sound`,
  `certified_verify_complete`, and `certified_certb_iff`: local rules,
  complete line lists, diagnostic agreement, requested conclusions,
  arithmetic soundness, arithmetic representational completeness, and
  independent payload replay respectively. The remaining reports certify
  legacy arithmetic agreement and accepted-result shape.

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

Redirect "theories/A002/_appendix/_assumptions/normalized_failure_index_none_iff"
  Print Assumptions normalized_failure_index_none_iff.

Redirect "theories/A002/_appendix/_assumptions/normalized_verifyb_iff"
  Print Assumptions normalized_verifyb_iff.

Redirect "theories/A002/_appendix/_assumptions/certified_verify_accept_sound"
  Print Assumptions certified_verify_accept_sound.

Redirect "theories/A002/_appendix/_assumptions/certified_verify_complete"
  Print Assumptions certified_verify_complete.

Redirect "theories/A002/_appendix/_assumptions/certified_verify_accept_payload"
  Print Assumptions certified_verify_accept_payload.

Redirect "theories/A002/_appendix/_assumptions/certified_certb_iff"
  Print Assumptions certified_certb_iff.

Redirect "theories/A002/_appendix/_assumptions/certified_generated_cert_checks"
  Print Assumptions certified_generated_cert_checks.

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
  A002_Verify A002_Certb A002_Verify_certified A002_Certified_Certb
  NormalizedFormula NormalizedRule NormalizedLine
  normalized_formula_eqb normalized_stepb normalized_linesb
  normalized_failure_index normalized_conclusion normalized_verifyb
  normalized_rejection
  normalize_formula normalize_rule normalize_line
  normalize_lines normalize_derivation
  normalized_formula_height encode_normalized_formula_raw
  encode_normalized_formula encode_normalized_rule
  encode_normalized_line encode_normalized_lines
  encode_normalized_derivation certified_payload
  code_var code_imp code_line tag_axk tag_axs tag_mp code_derivation
  parse_imp parse_line
  check_axk check_axs check_mp.

Extraction "theories/A002/_appendix/_artifacts/A002_IO"
  A002_IO A002_IO_Z
  A002_Verified A002_Certificate_Check
  A002_Parse_Formula A002_Parse_Line
  Decode_Result Decode_Error
  Verify_Diagnostic Verify_Diagnostic_Z.
