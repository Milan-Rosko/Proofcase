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

  Public API surface for A002. A single import exposes arithmetic
  normalization, target-sensitive inductive verification, the end-to-end
  certified arithmetic entry point, local and derivation reflection theorems,
  plus the legacy compatibility verifier, constructors, parsers, Hilbert-rule
  checkers, certificate agreement surface, and IO dispatcher.

  Downstream logical developments should prefer `NormalizedProof` and
  `normalized_verifyb_iff`; arithmetic clients should use
  `A002_Verify_certified`, whose acceptance theorem is
  `certified_verify_accept_sound`. The legacy arithmetic functions remain
  public for compatibility; artifact generation and sanity probes are
  excluded from this stable dependency boundary.

*)

From A002 Require Export A002_94_IO.
