(* T000__Comprehension.v *)

(* 
╔══════════════╗
║              ║
║   TEMPLATE   ║
║              ║
╚══════════════╝
*)

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                           COMPREHENSION LAYER                           │
│                                                                         │
│                                    .                                    │
│                                    -                                    │
│                                   ___                                   │
│                        `  .    .'     `.     .  ´                       │
│                               /         \                               │
│                              |           |                              │
│                      _  .    |           |    .  _                      │
│                               .  :~~~:  .                               │
│                                `. \ / .'                                │
│                            .     |_|_|     .                            │
│                           ´      (===)      `                           │
│                                   `-´                                   │
│                                                                         │
│     This file serves as a proof-semantic synopsis and comprehension     │
│     aid for project T000. It introduces no new constructive content     │
│     or derivations; but consolidates the pinned metadata, artifact      │
│     semantics, certification gates, and bounded endpoints into one      │
│     unified structure for readability and auditability.                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
  Proofcase / T000 / Comprehension Layer
  ======================================

    Overview
    --------

      WARNING. DO NOT ALTER.

      This file is an actual proof artifact in the T000 development, but it
      is also written as a canonical comprehension template for the project
      line. It re-exports the live definitions and theorems of the theory
      while organizing them in a standard audit-facing format.

      The numbering scheme is part of that template. Roman numerals
      `(i), (ii), (iii), ...` mark the major semantic layers of the file.
      Within each layer, Arabic numerals `(1), (2), (3), ...` enumerate the
      individual exported definitions, lemmas, or endpoints. The surrounding
      prose is meant to explain what each item contributes semantically, so
      the file can be read both as checked Coq code and as a structured guide
      to the proof architecture.

    Contents
    --------

      `T000` has one arithmetic route and one combinatorial closure route.

      (i) CORE ARITHMETIC DEFINITION LAYER

          `R01` explains how to split a positive number into two meaningful
          parts: the odd piece that remains after all factors of `2` have been
          removed, and the count of how many times `2` was removed. This gives
          the basic arithmetic viewpoint used in the rest of the package.

      (ii) BOUNDS AND STRUCTURE OF odd_part_aux

          `R01` records the auxiliary boundedness, oddness, and divisibility
          lemmas that control the fuel-indexed odd-part recursion.

      (iii) PUBLIC-FACING PROPERTIES OF odd_part

          `R01` proves that the public odd-part map is odd, bounded, positive,
          and divisive on positive inputs.

      (iv) DECOMPOSITION AND DIVISIBILITY BRIDGE

          `R01` establishes the factorization
          `n = 2^(val2 n) * odd_part n` and derives
          `same_odd_part_divides`.

      (v) PIGEONHOLE CODOMAIN CONSTRUCTION

          `R01` constructs the explicit codomain `odd_range n` of odd numbers
          in `{1, ..., 2n}`, and proves its length, membership
          characterization, bounds, non-duplication, and the landing theorem
          `odd_part_in_range`.

      (vi) LIST-BASED PIGEONHOLE PRINCIPLE

          `R02` proves the abstract list pigeonhole theorem and combines it
          with the odd-core codomain and divisibility bridge to obtain the
          closed theorem `pigeonhole_divisibility`.
*)

From Coq Require Import Arith Bool List PeanoNat.
Import ListNotations.

From T000 Require Import
  R01__Odd_Part
  R02__Pigeonhole_Divisibility.


Section Proof_Index.

(* 
║ (i)
║
║ CORE ARITHMETIC DEFINITIONS
║
*)

Definition audit_odd_part_aux : nat -> nat -> nat :=
  odd_part_aux.

(*
│  (1)
│
│  We begin by computing the odd
│  core of a natural number.
│  Semantically, we keep halving
│  even inputs until no factor of
│  `2` remains, and the fuel
│  parameter serves only to make
│  that descent structurally
│  explicit.
│
*)

Definition audit_odd_part : nat -> nat :=
  odd_part.

(*
│  (2)
│
│  We then package that
│  construction as the canonical
│  odd core of `n`, namely the
│  maximal odd divisor that
│  remains after all powers of
│  `2` have been removed.
│
*)

Definition audit_val2_aux : nat -> nat -> nat :=
  val2_aux.

(*
│  (3)
│
│  In parallel, we count the
│  dyadic depth of the same
│  process. Semantically, we
│  record how many halving steps
│  are needed before the odd core
│  is reached, again using fuel
│  only to justify structural
│  recursion.
│
*)

Definition audit_val2 : nat -> nat :=
  val2.

(*
│  (4)
│
│  We expose this dyadic depth as
│  the `2`-adic valuation, that
│  is, the exponent of the
│  largest power of `2` dividing
│  the input.
│
*)

(*
║ (ii)
║
║ BOUNDS AND STRUCTURE OF odd_part_aux
║
*)

Definition audit_odd_part_aux_le :=
  odd_part_aux_le.

(*
│  (1)
│
│  We record that the auxiliary
│  odd-part procedure is
│  non-expansive. We show that
│  every recursive step preserves
│  or decreases the input value.
│
*)

Definition audit_odd_part_aux_odd :=
  odd_part_aux_odd.

(*
│  (2)
│
│  Under the positivity and fuel
│  hypotheses used in `R01`, we
│  show that the auxiliary
│  procedure terminates at an odd
│  value.
│
*)

Definition audit_odd_part_aux_divides :=
  odd_part_aux_divides.

(*
│  (3)
│
│  Under the same hypotheses, we
│  show that the auxiliary output
│  still divides the original
│  number.
│
*)

(*
║ (iii)
║
║ PUBLIC-FACING PROPERTIES OF odd_part
║
║
*)

Definition audit_odd_part_odd :=
  odd_part_odd.

(*
│  (1)
│
│  We prove that for every
│  positive input, the extracted
│  odd part is odd.
│
*)

Definition audit_odd_part_le :=
  odd_part_le.

(*
│  (2)
│
│  We note that removing factors
│  of `2` cannot increase
│  magnitude.
│
*)

Definition audit_odd_part_pos :=
  odd_part_pos.

(*
│  (3)
│
│  We show that on positive
│  inputs, the odd part remains
│  positive.
│
*)

Definition audit_odd_part_divides :=
  odd_part_divides.

(*
│  (4)
│
│  We show that the odd part is
│  an actual divisor of the
│  original input.
│
*)

(*
║ (iv)
║
║ DECOMPOSITION AND DIVISIBILITY BRIDGE
║
*)

Definition audit_decomposition_aux :=
  decomposition_aux.

(*
│  (1)
│
│  We first record the auxiliary
│  factorization. We track the
│  recursion explicitly through
│  the fuel parameter.
│
*)

Definition audit_decomposition :=
  decomposition.

(*
│  (2)
│
│  We expose the canonical identity
│  `n = 2^(val2 n) * odd_part n`
│  for positive naturals.
│
*)

Definition audit_same_odd_part_divides :=
  same_odd_part_divides.

(*
│  (3)
│
│  We show that if two positive
│  naturals have the same odd
│  part, their dyadic exponents
│  linearly order the two
│  decompositions. We then
│  conclude that one number
│  divides the other.
│
*)

(*
║ (v)
║
║ PIGEONHOLE CODOMAIN CONSTRUCTION
║
*)

Definition audit_odd_range : nat -> list nat :=
  odd_range.

(*
│  (1)
│
│  We enumerate the odd numbers
│  in `{1, ..., 2n}` by this
│  list.
│
*)

Definition audit_odd_range_length :=
  odd_range_length.

(*
│  (2)
│
│  We prove that this codomain
│  contains exactly `n` entries.
│
*)

Definition audit_odd_range_in_iff :=
  odd_range_in_iff.

(*
│  (3)
│
│  We characterize membership by
│  the representation
│  `2 * i + 1` with `i < n`.
│
*)

Definition audit_odd_range_all_odd :=
  odd_range_all_odd.

(*
│  (4)
│
│  We verify that every element
│  of `odd_range n` is odd.
│
*)

Definition audit_odd_range_bounds :=
  odd_range_bounds.

(*
│  (5)
│
│  We bound every element
│  between `1` and `2n - 1`.
│
*)

Definition audit_odd_range_NoDup :=
  odd_range_NoDup.

(*
│  (6)
│
│  We prove that this
│  enumeration has no duplicate
│  entries.
│
*)

Definition audit_odd_part_in_range :=
  odd_part_in_range.

(*
│  (7)
│
│  We show that any `a` with
│  `1 <= a <= 2n` is sent by
│  `odd_part` into the finite
│  codomain `odd_range n`. We use
│  this as the counting fact
│  needed for the pigeonhole
│  step.
│
*)

(*
║ (vi)
║
║ LIST-BASED PIGEONHOLE PRINCIPLE
║
*)

Definition audit_pigeonhole :=
  pigeonhole.

(*
│  (1)
│
│  We expose the list-based
│  pigeonhole principle. We show
│  that a NoDup source list
│  mapping into a strictly
│  smaller target list must
│  contain a collision.
│
*)

Definition audit_pigeonhole_divisibility :=
  @pigeonhole_divisibility.

(* 
│  (2)
│
│  We expose the main theorem. We
│  prove that any NoDup list of
│  length `n + 1` contained in
│  `{1, ..., 2n}` contains two
│  distinct elements related by
│  divisibility.
│
*)


End Proof_Index.

(*
╔═══════════════╗
║               ║
║   CHECKLIST   ║
║               ║
╚═══════════════╝

  FILE IDENTITY
  -------------

    [ ] File name and first-line header match exactly:
        `T<nnn>__Comprehension.v`.
    [ ] The file begins with the canonical ASCII-art banner and
        synopsis stating:
          - no new constructive content,
          - audit/comprehension purpose,
          - correct project number.

  OVERVIEW STRUCTURE
  ---------------------

    [ ] The overview block starts with:
            Proofcase / T<nnn> / Comprehension Layer
    [ ] The line `WARNING. DO NOT ALTER.` appears verbatim.
    [ ] The overview explains:
          - dual role (artifact + template),
          - re-export structure,
          - numbering convention (roman / arabic).

  CONTENTS SECTION
  ----------------

    [ ] A `Contents` section lists all major layers `(i), (ii), ...`.
    [ ] Each layer includes a short description and references the
        corresponding route files (`R01`, `R02`, ...).
    [ ] The listed layers match exactly those implemented below.

  IMPORTS
  -------

    [ ] All route files used in the index are imported, in order.

  STRUCTURAL FRAME
  -------------------

    [ ] All audit aliases are inside `Section Proof_Index.` ...
      `End Proof_Index.`.
    [ ] Only `Definition audit_<name> := <name>.` entries appear
        (no proofs, tactics, or new constructions).

  LAYER AND ITEM ORGANIZATION
  ---------------------------

    [ ] Each layer is introduced by a `(i), (ii), ...` header with
        an ALL-CAPS title.
    [ ] Each item:
          - has an Arabic index `(1), (2), ...`,
          - is followed by exactly one audit definition,
          - appears in dependency order.
    [ ] Numbering is sequential; item indices reset per layer.

  PROSE DISCIPLINE
  ----------------

    [ ] Explanations use concise, present-tense statements
        ("We show", "We prove", "We record").
    [ ] Each comment explains semantic meaning, not proof tactics.
    [ ] Identifiers appear in backticks; no external formatting
        (markdown, emojis, etc.) is used.

  COVERAGE AND CONSISTENCY
  ------------------------

    [ ] Every exported definition/theorem from the route files
        appears exactly once.
    [ ] The ordering reflects logical dependency.
    [ ] The file compiles cleanly and introduces no new axioms.
    [ ] The file is readable as a standalone structural guide.
*)
