(* T000__Comprehension.v *)

From Coq Require Import Arith Bool List PeanoNat.
Import ListNotations.

From T000 Require Import
  R01__Odd_Part
  R02__Pigeonhole_Divisibility.

(*************************************************************************)
(*                                   .                                   *)
(*                                  ___                                  *)
(*                       `  .    .'     `.     .  ´                      *)
(*                              /         \                              *)
(*                             |           |                             *)
(*                     _  .    |           |    .  _                     *)
(*                              .  :~~~:  .                              *)
(*                               `. \ / .'                               *)
(*                           .     |_|_|     .                           *)
(*                          ´      (===)      `                          *)
(*                                  `-´                                  *)
(*                                                                       *)
(*    Proofcase / T000 -- Comprehension Layer                            *)
(*                                                                       *)
(*    This file serves as a proof-semantic synopsis and comprehension    *)
(*    aid for project T000. It introduces no new constructive content    *)
(*    or  derivations; but consolidates the core semantics (theorems,    *)
(*    lemmas,  and corollaries, together with their endpoints) into a    *)
(*    unified structure for readability and auditability.                *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*

Proofcase / T000 / Comprehension
================================
  
  Overview
  --------

  `T000` has two routes: an arithmetic layer and a combinatorial layer.

  (i) ODD-PART DEFINITION LAYER

      `R01` defines the odd-part map and the 2-adic valuation in plain
      `nat` terms: `odd_part_aux` strips factors of 2 with a fuel
      parameter, `odd_part` instantiates it, and `val2` / `val2_aux`
      count the extracted factors.

  (ii) ODD-PART PROPERTIES LAYER

      `R01` establishes the core arithmetic facts: `odd_part` is odd,
      bounded, positive, and divides its argument; every positive
      integer decomposes as `2^(val2 n) * odd_part n`; and the key
      bridge theorem `same_odd_part_divides` shows that sharing the
      same odd part implies divisibility.

  (iii) ODD RANGE LAYER

      `R01` builds the explicit pigeonhole codomain: the list
      `odd_range n` of the n odd numbers in {1, ..., 2n}, and proves
      its length, membership characterization, bounds, and that the
      odd-part map lands in this list.

  (iv) PIGEONHOLE AND MAIN THEOREM LAYER

      `R02` proves a list-based pigeonhole principle, then combines it
      with the odd-part infrastructure from `R01` to derive the main
      theorem: any n+1 distinct elements of {1, ..., 2n} contain a
      divisibility pair.
*)

(*************************************************************************)
(*                                                                       *)
(*                       ODD-PART DEFINITION LAYER                       *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  CORE ARITHMETIC DEFINITIONS
*)

Definition audit_odd_part_aux : nat -> nat -> nat :=
  odd_part_aux.

Definition audit_odd_part : nat -> nat :=
  odd_part.

Definition audit_val2_aux : nat -> nat -> nat :=
  val2_aux.

Definition audit_val2 : nat -> nat :=
  val2.

(*************************************************************************)
(*                                                                       *)
(*                      ODD-PART PROPERTIES LAYER                        *)
(*                                                                       *)
(*************************************************************************)

(*
  (ii)
  BOUNDS AND STRUCTURE OF odd_part_aux
*)

Definition audit_odd_part_aux_le :=
  odd_part_aux_le.

Definition audit_odd_part_aux_odd :=
  odd_part_aux_odd.

Definition audit_odd_part_aux_divides :=
  odd_part_aux_divides.

(*
  (iii)
  PUBLIC-FACING PROPERTIES OF odd_part
*)

Definition audit_odd_part_odd :=
  odd_part_odd.

Definition audit_odd_part_le :=
  odd_part_le.

Definition audit_odd_part_pos :=
  odd_part_pos.

Definition audit_odd_part_divides :=
  odd_part_divides.

(*
  (iv)
  DECOMPOSITION AND DIVISIBILITY BRIDGE
*)

Definition audit_decomposition_aux :=
  decomposition_aux.

Definition audit_decomposition :=
  decomposition.

(*
  Key bridge theorem: if two positive integers share the same odd
  part, one divides the other.
*)

Definition audit_same_odd_part_divides :=
  same_odd_part_divides.

(*************************************************************************)
(*                                                                       *)
(*                           ODD RANGE LAYER                             *)
(*                                                                       *)
(*************************************************************************)

(*
  (v)
  PIGEONHOLE CODOMAIN CONSTRUCTION
*)

Definition audit_odd_range : nat -> list nat :=
  odd_range.

Definition audit_odd_range_length :=
  odd_range_length.

Definition audit_odd_range_in_iff :=
  odd_range_in_iff.

Definition audit_odd_range_all_odd :=
  odd_range_all_odd.

Definition audit_odd_range_bounds :=
  odd_range_bounds.

Definition audit_odd_range_NoDup :=
  odd_range_NoDup.

(*
  The counting lemma: the odd part of any element of {1, ..., 2n}
  belongs to the n-element list odd_range n.
*)

Definition audit_odd_part_in_range :=
  odd_part_in_range.

(*************************************************************************)
(*                                                                       *)
(*                  PIGEONHOLE AND MAIN THEOREM LAYER                    *)
(*                                                                       *)
(*************************************************************************)

(*
  (vi)
  LIST-BASED PIGEONHOLE PRINCIPLE
*)

Definition audit_pigeonhole :=
  pigeonhole.

(*
  Main theorem: any n+1 distinct elements drawn from {1, ..., 2n}
  contain two distinct elements where one divides the other.

  The theorem is section-parametric in n, A, and three hypotheses
  (boundedness, distinctness, cardinality).
*)

Definition audit_pigeonhole_divisibility :=
  @pigeonhole_divisibility.

(*************************************************************************)
(*                                                                       *)
(*                        Pigeonhole Divisibility                        *)
(*                                                                       *)
(*                             PROOF SKETCH                              *)
(*                                                                       *)
(*    Step 1. Decompose every element a in A as a = 2^k * odd_part(a)    *)
(*            where odd_part(a) is odd.  The odd-part map sends each     *)
(*            element of {1, ..., 2n} to one of the n odd numbers        *)
(*            in {1, 3, 5, ..., 2n - 1}.                                 *)
(*                                                                       *)
(*    Step 2. Since A has n + 1 elements and there are only n odd        *)
(*            pigeonholes, by the pigeonhole principle two distinct      *)
(*            elements a, b in A satisfy odd_part(a) = odd_part(b).      *)
(*                                                                       *)
(*    Step 3. Since a = 2^j * m and b = 2^k * m share the same odd       *)
(*            factor m, the element with the smaller 2-adic valuation    *)
(*            divides the other.                                         *)
(*                                                                       *)
(*                             MECHANIZATION                             *)
(*                                                                       *)
(*    forall n A,                                                        *)
(*      (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->                    *)
(*      NoDup A ->                                                       *)
(*      length A = n + 1 ->                                              *)
(*      exists a b,                                                      *)
(*        In a A /\ In b A /\ a <> b /\                                  *)
(*        (Nat.divide a b \/ Nat.divide b a)                             *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Under  the  explicit  pigeonhole  argument  carried  in  `R02`,    *)
(*    the  theorem  is  fully  closed:  any  sufficiently  large  set    *)
(*    of  naturals  drawn  from  {1, ..., 2n}  necessarily  contains     *)
(*    a  divisibility  pair.  The  bridge  lemma  `same_odd_part_        *)
(*    divides`  converts  an  odd-part  collision  into divisibility.    *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    T000  is intended to be fully closed: the assumption reports at    *)
(*    the end of `T000__QED.v` confirm that no axioms beyond the Rocq    *)
(*    kernel are used.                                                   *)
(*                                                                       *)
(*************************************************************************)

End Proof_Index.
