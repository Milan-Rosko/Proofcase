(* T000__QED.v *)

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
│     ________________________  _________________                         │
│     ___________________  __ \ ___  ____/__  __ \                        │
│     __________________  / / / __  __/  __  / / /                        │
│     _________________/ /_/ /___  /______  /_/ /__                       │
│     _________________\___\_\(_)_____/(_)_____/_(_)                      │
│                                                                         │
│                                                                         │
│     This file states an exact public target, the Rocq-side criteria     │
│     required  by  the reductions, certifies each endpoint by direct     │
│     reuse, and exposes the key assumption reports.                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
  Proofcase / T000 / Certification Layer
  ======================================

    Overview
    --------

      WARNING. DO NOT ALTER.

      This file is the terminal proof artifact of the T000 development. It
      fixes the public statement, certifies it by direct reuse of the
      reduction pipeline, and exposes the assumption footprint of the
      resulting theorem.

      At the same time, the file follows the canonical comprehension
      template used across the project line. The code is therefore arranged
      not only for execution and extraction, but also for auditability.

      The structure is layered. The central proposition (`PROPOSITIO`)
      isolates the exact public contract. `pigeonhole_divisibility_QED` closes
      this contract by direct reference to the constructed proof.
      
      The subsequent extraction interface presents executable counterparts
      of the core constructions, while the final reports make all remaining
      assumptions explicit.

      Proof: PIGEONHOLE DIVISIBILITY

      Source: Erdős anecdote as described by Aigner in “Proofs from THE BOOK”

      Let n be a positive natural number and let A be a finite collection
      of n + 1 pairwise distinct elements drawn from the interval
      {1, 2, ..., 2n}.  Then A necessarily contains two distinct elements
      a and b such that a divides b or b divides a.

    Contents
    --------

      PROPOSITIO
      
      The public contract specialized to the pigeonhole divisibility
      theorem. It formalizes that any collection of n + 1 distinct
      elements drawn from {1, ..., 2n} must contain a pair where one
      divides the other.

      Q.E.D.

      Certification of the pigeonhole statement. The theorem is closed
      by direct reuse of the constructed result, which combines the
      odd-part decomposition with the pigeonhole argument to produce
      the required divisible pair.

      EXTRACTION

      Executable interface reflecting the combinatorial and arithmetic
      structure of the proof. It provides computable counterparts for
      odd parts, range construction, collision detection, and witness
      extraction for divisibility.

      ASSUMPTION REPORT

      Explicit disclosure of logical dependencies used in establishing
      the pigeonhole divisibility result, ensuring that the final
      theorem is fully transparent with respect to its proof base.
*)

From Coq Require Import Arith Bool Extraction List PeanoNat.
Import ListNotations.

From T000 Require Import
  R01__Odd_Part
  R02__Pigeonhole_Divisibility.


(*************************************************************************)
(*                                                                       *)
(*                              PROPOSITIO                               *)
(*                                                                       *)
(*************************************************************************)


  (*
  ║ (i)
  ║ CONTRACT ONE
  *)

  (*
  │  (1)
  │  We formally state the pigeonhole
  │  divisibility theorem as a contract:
  │
  │  For every natural number `n` and
  │  every list `A`, if all elements of
  │  `A` lie in the interval `{1, ...,
  │  2n}`, if no element is repeated,
  │  and if the list has length `n + 1`,
  │  then there exist two distinct
  │  elements of `A` such that one
  │  divides the other.
  *)

Definition PROPOSITIO : Prop :=
  forall n A,
    (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->
    NoDup A ->
    length A = n + 1 ->
    exists a b,
      In a A /\
      In b A /\
      a <> b /\
      (Nat.divide a b \/ Nat.divide b a).

(*************************************************************************)
(*                                                                       *)
(*                                Q.E.D.                                 *)
(*                                                                       *)
(*************************************************************************)

  (*
  ║ (i)
  ║ DISCHARGE OF CONTRACT ONE
  *)

  (*
  │  (1)
  │  We discharge the public contract
  │  by direct reuse of the theorem
  │  `pigeonhole_divisibility`.
  │
  │  No further proof transformation is
  │  performed at this stage: the final
  │  endpoint is obtained by identifying
  │  `PROPOSITIO` with the already
  │  established divisibility result.
  *)

Theorem pigeonhole_divisibility_QED : PROPOSITIO.
Proof.
  exact pigeonhole_divisibility.
Qed.

(*************************************************************************)
(*                                                                       *)
(*                           OCaml Extraction                            *)
(*                                                                       *)
(*************************************************************************)

Section Extraction_Interface.

(*
║  (i)
║  ODD-PART DATA AND BASIC PROJECTIONS
*)

(*
│  (1)
│  We package, for a given natural
│  number, its 2-adic valuation
│  together with its odd part.
│
│  This pair represents the canonical
│  decomposition used throughout the
│  proof.
*)

Definition odd_part_data (n : nat) : nat * nat :=
  (val2 n, odd_part n).

(*
│  (2)
│  We extend the previous construction
│  pointwise to lists, producing the
│  dyadic profile of a finite family.
*)

Definition odd_part_profile (xs : list nat) : list (nat * nat) :=
  map odd_part_data xs.

(*
│  (3)
│  We expose the finite list of odd
│  numbers `{1, 3, ..., 2n - 1}` as a
│  concrete object.
│  This list serves as the codomain
│  of the odd-part map in the
│  pigeonhole argument.
*)

Definition odd_range_as_nat_list (n : nat) : list nat :=
  odd_range n.

(*
║  (ii)
║  BOOLEAN STRUCTURE ON LISTS
*)

(*
│  (1)
│  Boolean membership test for natural
│  numbers in a list.
│  It provides a computational
│  counterpart to propositional `In`.
*)

Fixpoint member_natb (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => orb (Nat.eqb x y) (member_natb x ys)
  end.

(*
│  (2)
│  Image of a list under the odd-part
│  map.
│  This realizes the projection used
│  in the pigeonhole step.
*)

Definition odd_part_image (xs : list nat) : list nat :=
  map odd_part xs.

(*
│  (3)
│  Check that every element of a list
│  belongs to a fixed reference list.
│  This encodes inclusion of images
│  into the finite codomain.
*)

Fixpoint all_members_ofb (cats xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (member_natb x cats) (all_members_ofb cats xs')
  end.

(*
│  (4)
│  Boolean formulation of the fact
│  that odd parts of inputs in
│  `{1, ..., 2n}` lie in `odd_range n`.
*)

Definition all_odd_parts_in_rangeb (n : nat) (xs : list nat) : bool :=
  all_members_ofb (odd_range_as_nat_list n) (odd_part_image xs).

(*
│  (5)
│  Boolean comparison of odd parts.
│  This detects the collisions that
│  drive the pigeonhole argument.
*)

Definition same_odd_partb (a b : nat) : bool :=
  Nat.eqb (odd_part a) (odd_part b).

(*
│  (6)
│  Boolean divisibility test, defined
│  via remainder computation and
│  excluding the degenerate zero
│  divisor.
*)

Definition dividesb (a b : nat) : bool :=
  match a with
  | 0 => false
  | S _ => Nat.eqb (Nat.modulo b a) 0
  end.

(*
║  (iii)
║  ENCODING OF INPUT CONSTRAINTS
*)

(*
│  (1)
│  Boolean check that a number lies in
│  the interval `{1, ..., 2n}`.
*)

Definition bounded_by_2n (n a : nat) : bool :=
  andb (Nat.leb 1 a) (Nat.leb a (2 * n)).

(*
│  (2)
│  Verify that all elements of a list
│  satisfy the interval constraint.
*)

Fixpoint all_elements_boundedb (n : nat) (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (bounded_by_2n n x) (all_elements_boundedb n xs')
  end.

(*
│  (3)
│  Boolean test for absence of
│  duplicates. This encodes the
│  `NoDup` condition.
│
*)

Fixpoint all_distinctb (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (negb (member_natb x xs')) (all_distinctb xs')
  end.

(*
│  (4)
│   Combined validation of the input
│   hypotheses of the theorem. This
│   packages boundedness, distinctness,
│   and cardinality.
*)

Definition valid_pigeonhole_instanceb (n : nat) (xs : list nat) : bool :=
  andb
    (all_elements_boundedb n xs)
    (andb
      (all_distinctb xs)
      (Nat.eqb (length xs) (S n))).

(*
║  (iv)
║  SEARCH FOR PIGEONHOLE COLLISIONS
*)

(*
│  (1)
│  For a fixed element, search the
│  remainder of the list for another
│  element with the same odd part.
│
*)

Fixpoint find_same_odd_part_partner
    (a : nat) (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | b :: xs' =>
      if same_odd_partb a b
      then Some b
      else find_same_odd_part_partner a xs'
  end.

(*
│  (2)
│  Scan the list to find the first
│  pair with equal odd parts.
│  This realizes the pigeonhole
│  collision at the computational
│  level.
*)

Fixpoint find_same_odd_part_pair
    (xs : list nat) : option (nat * nat) :=
  match xs with
  | [] => None
  | a :: xs' =>
      match find_same_odd_part_partner a xs' with
      | Some b => Some (a, b)
      | None => find_same_odd_part_pair xs'
      end
  end.

(*
║  (v)
║  EXTRACTION OF DIVISIBILITY WITNESSES
*)

(*
│  (1)
│  Finite type recording the possible
│  orientations of divisibility.
*)

Inductive DivisibilityDirection : Type :=
| Pdw_left_divides_right
| Pdw_right_divides_left.

(*
│  (2)
│  Finite result type describing the
│  outcome of the witness search.
│  It distinguishes invalid inputs,
│  absence of collision, and successful
│  certification.
│
*)

Inductive PigeonholeDivisibilityWitnessResult : Type :=
| Pdwr_invalid_input
| Pdwr_no_collision_found
| Pdwr_collision_without_divisibility :
    nat -> nat -> nat -> PigeonholeDivisibilityWitnessResult
| Pdwr_witness :
    nat -> nat -> nat -> DivisibilityDirection ->
    PigeonholeDivisibilityWitnessResult.

(*
│  (3)
│  Determine the direction of
│  divisibility for a candidate pair.
*)

Definition classify_divisibility_direction
    (a b : nat) : option DivisibilityDirection :=
  if dividesb a b
  then Some Pdw_left_divides_right
  else
    if dividesb b a
    then Some Pdw_right_divides_left
    else None.

(*
│  (4)
│  Construct an explicit witness from
│  a detected collision.
*)

Definition build_witness_from_collision
    (a b : nat) : PigeonholeDivisibilityWitnessResult :=
  let shared_odd_part := odd_part a in
  match classify_divisibility_direction a b with
  | Some direction =>
      Pdwr_witness a b shared_odd_part direction
  | None =>
      Pdwr_collision_without_divisibility a b shared_odd_part
  end.

(*
│  (5)
│   Full finite procedure mirroring the
│   theorem: validate the input, detect
│   a collision, and extract a
│   divisibility witness.
*)

Definition search_pigeonhole_divisibility_witness
    (n : nat) (xs : list nat) : PigeonholeDivisibilityWitnessResult :=
  if valid_pigeonhole_instanceb n xs
  then
    match find_same_odd_part_pair xs with
    | Some (a, b) => build_witness_from_collision a b
    | None => Pdwr_no_collision_found
    end
  else Pdwr_invalid_input.

End Extraction_Interface.

(*
│  (6)
│  Extraction.
*)

Set Extraction Output Directory "appendix/extracted".
Extraction Language OCaml.

Extraction "OddPartComputations.ml"
  odd_part_aux
  odd_part
  val2_aux
  val2
  odd_part_data
  odd_part_profile
  odd_range_as_nat_list
  odd_part_image
  all_odd_parts_in_rangeb.

Extraction "PigeonholeDivisibilityWitness.ml"
  odd_part
  odd_range_as_nat_list
  member_natb
  same_odd_partb
  dividesb
  valid_pigeonhole_instanceb
  find_same_odd_part_pair
  search_pigeonhole_divisibility_witness.

(*************************************************************************)
(*                                                                       *)
(*                              ASSUMPTIONS                              *)
(*                                                                       *)
(*************************************************************************)

(* 
│  (1)
│  We audit the assumption
│  footprint of the construction.
│  For each intermediate theorem
│  and for the final endpoint, we
│  query the kernel for remaining
│  axioms. The intended outcome is
│  closedness: no unproven
│  assumptions beyond the standard
│  environment.
│
*)

Print Assumptions same_odd_part_divides.
Print Assumptions pigeonhole.
Print Assumptions pigeonhole_divisibility.

(* 
│  (2)
│  We persist the assumption
│  report of the final theorem as
│  a certificate artifact.
│  This externalizes the kernel
│  check and makes the closedness
│  of `pigeonhole_divisibility_QED`
│  inspectable in the build
│  output.
*)

Redirect "theories/T000/appendix/assumptions/pigeonhole_divisibility_QED"
  Print Assumptions pigeonhole_divisibility_QED.

(*
╔═══════════════╗
║               ║
║   CHECKLIST   ║
║               ║
╚═══════════════╝

  FILE IDENTITY

    [ ] File name and first-line header match exactly:
        `T<nnn>__QED.v`.
    [ ] The file begins with the canonical ASCII-art banner and
        synopsis stating:
          - exact public-target role,
          - direct certification role,
          - assumption-report role,
          - correct project number.

  OVERVIEW STRUCTURE

    [ ] The overview block starts with:
            Proofcase / T<nnn> / Certification Layer
    [ ] The line `WARNING. DO NOT ALTER.` appears verbatim.
    [ ] The overview explains:
          - public contract,
          - direct reuse of the established theorem,
          - extraction interface,
          - assumption transparency.

  CONTENTS SECTION

    [ ] A `Contents` section lists:
          - `PROPOSITIO`,
          - `Q.E.D.`,
          - `EXTRACTION`,
          - `ASSUMPTION REPORT`.
    [ ] Each item includes a short semantic description.
    [ ] The listed sections match exactly those implemented below.

  IMPORTS

    [ ] Standard-library imports include extraction support.
    [ ] All route files needed by the public surface are imported, in order.

  PUBLIC CONTRACT

    [ ] `PROPOSITIO` states the exact public theorem contract.
    [ ] The contract quantifies the boundedness, distinctness, and
        cardinality hypotheses explicitly.
    [ ] The conclusion states existence of two distinct inputs related
        by divisibility.

  Q.E.D.

    [ ] The principal theorem is named `<public theorem>_QED`.
    [ ] The proof discharges the contract by direct reuse of the
        established theorem, with no additional proof layer.

  EXTRACTION INTERFACE
  --------------------

    [ ] Executable definitions are grouped inside
        `Section Extraction_Interface.` ... `End Extraction_Interface.`.
    [ ] The interface exposes arithmetic projections, list checks,
        collision search, and witness construction.
    [ ] Extraction directives target the checked-in artifacts directory.
    [ ] Extracted filenames match the package tree and appendix layout.

  ASSUMPTION REPORT
  -----------------

    [ ] `Print Assumptions` is issued for the principal intermediate
        and final theorems.
    [ ] A `Redirect` command persists the final assumption report to the
        appendix assumptions artifact.

  PROSE DISCIPLINE
  ----------------

    [ ] Explanations use concise, present-tense statements
        ("We state", "We discharge", "We expose").
    [ ] Each comment explains semantic meaning, not proof tactics.
    [ ] Identifiers appear in backticks; no external formatting
        (markdown, emojis, etc.) is used.

  COVERAGE AND CONSISTENCY
  ------------------------

    [ ] The file contains the public contract, the terminal theorem,
        the extraction surface, and the assumption report.
    [ ] Artifact paths named in the file agree with the package layout.
    [ ] The file is readable as a standalone certification surface.
*)
