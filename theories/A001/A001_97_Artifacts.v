(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Artifact layer for A001. We record assumption reports for the citation theorems and extract the certified pairing functions, together with the inspection interface, to OCaml.]]@*)

(*@head.end@*)

From A001 Require Import A001_05__Pair_Unpair_Correct.
From A001 Require Import A001_94_IO.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatBigInt.

Redirect "theories/A001/_appendix/_assumptions/decode_encode"
  Print Assumptions decode_encode.

Redirect "theories/A001/_appendix/_assumptions/encode_injective"
  Print Assumptions encode_injective.

Extraction Inline base_params Z r B.
Extraction Inline Paired_AB Unpaired_C.
Extraction Language OCaml.

Extraction "theories/A001/_appendix/_artifacts/A001_Encode_Decode"
  encode decode.

Extraction "theories/A001/_appendix/_artifacts/A001_Carryless_Pairing_IO"
  A001_IO Pair_IO Unpair_IO
  Check_Pairing In_Imageb Status_Of_Code.
