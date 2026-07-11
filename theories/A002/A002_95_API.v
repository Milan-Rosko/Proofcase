(*A002_95_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / A002_95_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Public API surface for A002. A single import exposes the normalized
  formula/rule/line types, structural checker and reflection theorems,
  together with the arithmetic compatibility verifier, constructors, parsers,
  Hilbert-rule checkers, certificate agreement surface, and IO dispatcher.

  Downstream logical developments should prefer `NormalizedFormula`,
  `NormalizedStep`, `NormalizedLines`, `normalized_stepb_iff`, and
  `normalized_linesb_iff`. The arithmetic functions remain public for
  serialization and extracted compatibility; artifact generation and sanity
  probes are intentionally excluded from this stable dependency boundary.

*)

From A002 Require Export A002_94_IO.
