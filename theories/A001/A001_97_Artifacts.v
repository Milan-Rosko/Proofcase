(*A001_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / A001_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Artifact layer for A001. We record assumption reports for the citation
  theorems and extract the certified pairing functions, together with the
  inspection interface, to OCaml.

*)

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

Extraction "A001_Encode_Decode" encode decode.

Extraction "A001_Carryless_Pairing_IO"
  A001_IO Pair_IO Unpair_IO
  Check_Pairing In_Imageb Status_Of_Code.
