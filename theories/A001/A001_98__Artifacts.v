(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This driver file isolates assumption reports and extraction commands for A001. The proof-facing theory files remain import-safe, while artifact generation is still available through a single explicit entry point.]]@*)

(*@head.end@*)

From A001 Require Import A001_99_IO.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatBigInt.

Redirect "theories/A001/appendix/assumptions/decode_encode"
  Print Assumptions decode_encode.

Redirect "theories/A001/appendix/assumptions/encode_injective"
  Print Assumptions encode_injective.

Extraction Inline base_params Z r B.
Extraction Inline Paired_AB Unpaired_C.

Extraction Language OCaml.
Extraction "carryless_pairing" encode decode.

Extraction "carryless_pairing_io"
  A001_IO Pair_IO Unpair_IO
  Check_Pairing In_Imageb Status_Of_Code.
