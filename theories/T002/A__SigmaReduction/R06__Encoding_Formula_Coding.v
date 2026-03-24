(*

  Proofcase / T002 / Encoding Formula Coding
  ==========================================

    Overview
    --------

      We develop the Encoding Formula Coding layer used by the T002 sigma-
      reduction route. This file packages the definitions and lemmas
      exported to later modules in the same route.
*)

From Coq Require Import Arith.
From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax.

Fixpoint enc_form (phi : Form) : nat :=
  match phi with
  | F_Bot => 0
  | F_Imp a b => S (pair P0 (enc_form a) (enc_form b))
  end.
