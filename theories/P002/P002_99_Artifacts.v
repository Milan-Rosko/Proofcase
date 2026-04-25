(*P002_99_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / P002_99_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Driver file for P002 artifact generation: terminal assumption reports and
  OCaml extraction of the executable surfaces. Isolated here so `P002_98_QED`
  remains proof-facing, while importing this file intentionally triggers
  artifact side effects.

  The extracted computational surface is intentionally small: one bounded
  constructive compiler artifact. The classical open wrapper and packed-mask
  proof surface are proof-facing only and are recorded through assumption
  reports, not OCaml extraction.

*)

(*
│
│          The artifact driver imports the closed Diophantine algebra,
│          the terminal proof layer, and the OCaml extraction back
│          ends.
│
*)

From P002 Require Import P002_12__Diophantine_Algebra.
From P002 Require Import P002_98_QED.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatBigInt.

(*
│
│          The bounded completeness assumption report records the
│          dependencies of the constructive endpoint.
│
*)

Redirect "theories/P002/appendix/_assumptions/N_BoundedCubicFamilySat_RE_complete_QED"
  Print Assumptions N_BoundedCubicFamilySat_RE_complete_QED.

(*
│
│          The unbounded completeness assumption report records the
│          dependencies of the classical family-level endpoint.
│
*)

Redirect "theories/P002/appendix/_assumptions/N_CubicFamilySat_RE_complete_QED"
  Print Assumptions N_CubicFamilySat_RE_complete_QED.

(*
│
│          The no-solver assumption report records the dependencies of
│          the conditional semantic undecidability corollary.
│
*)

Redirect "theories/P002/appendix/_assumptions/CubicFamily_no_solver_QED"
  Print Assumptions CubicFamily_no_solver_QED.

(*
│
│          The packed-mask Diophantine assumption report records the
│          closed carryless divisibility endpoint without forcing
│          modular OCaml extraction of the packed semantics graph.
│
*)

Redirect "theories/P002/appendix/_assumptions/packed_mask_diophantine_instance_with_wf"
  Print Assumptions packed_mask_diophantine_instance_with_wf.

(*
│
│          The trace-channel helpers are inlined in the extracted
│          OCaml for a smaller artifact surface.
│
*)

Extraction Inline trace_halt_var trace_code_var.

(*
│
│          The extraction language is OCaml.
│
*)

Extraction Language OCaml.

(*
│
│          The bounded cubic-family artifact extracts the constructive
│          witness search and family compiler.
│
*)

Extraction "P002_Bounded_Cubic_Family"
  search_FMValidTrace_upto
  emit_trace_family
  emit_bounded_witness_search_family
  compile_fm_family_upto
  cubic_family_count
  family_var_bound.
