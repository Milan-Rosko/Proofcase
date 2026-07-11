(*A002_98_Sanity.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                          Proofcase / A002_98_Sanity                          │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Two minimal effectivity witnesses for the normalized A002 checker. The
  first checks one K line; the second checks two K lines followed by modus
  ponens. Both use only inductive formulas, rules, lines, and ordinary lists,
  so no A001 arithmetic container is materialized.

  These are closed compile-time computations, not an additional theorem
  layer. General K/S/MP correctness and whole-derivation validity are already
  supplied by `normalized_stepb_iff` and `normalized_linesb_iff`; the probes
  only confirm that representative normalized programs reduce immediately.

*)

From A002 Require Import A002_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                K EFFECTIVITY                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `sanity_A` and `sanity_B` are two distinct normalized
│          propositional variables used to instantiate K.
│
*)

Definition sanity_A : NormalizedFormula :=
  NFVar 0.

Definition sanity_B : NormalizedFormula :=
  NFVar 1.

(*
│
│          `sanity_K` is the normalized K instance `A → (B → A)`.
│
*)

(*                          sanity_K ≔ A → (B → A).                           *)

Definition sanity_K : NormalizedFormula :=
  NFImp sanity_A (NFImp sanity_B sanity_A).

(*
│
│          The first derivation consists of the single K formula
│          tagged by the normalized K rule.
│
*)

Definition sanity_K_derivation : NormalizedDerivation :=
  [Build_NormalizedLine NRAxK sanity_K].

(*
│
│          The structural checker accepts the closed K derivation by
│          direct reduction.
│
*)

(*                   normalized_linesb([], [K(A,B)])=true.                    *)

Example sanity_normalized_K_checks :
  normalized_linesb [] sanity_K_derivation = true.
Proof.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           MODUS PONENS EFFECTIVITY                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The MP conclusion is `A → K`; its major premise `K → (A →
│          K)` is itself another K instance.
│
*)

Definition sanity_MP_conclusion : NormalizedFormula :=
  NFImp sanity_A sanity_K.

Definition sanity_MP_major : NormalizedFormula :=
  NFImp sanity_K sanity_MP_conclusion.

(*
│
│          The second derivation proves `K`, proves `K → (A → K)` by K
│          again, then cites lines `0` and `1` to obtain `A → K` by
│          MP.
│
*)

Definition sanity_MP_derivation : NormalizedDerivation :=
  [ Build_NormalizedLine NRAxK sanity_K;
    Build_NormalizedLine NRAxK sanity_MP_major;
    Build_NormalizedLine (NRMP 0 1) sanity_MP_conclusion ].

(*
│
│          The normalized checker resolves both prefix citations and
│          accepts the three-line derivation by direct reduction.
│
*)

(*                  [K, K→(A→K), MP(0,1,A→K)] checks = true.                  *)

Example sanity_normalized_MP_checks :
  normalized_linesb [] sanity_MP_derivation = true.
Proof.
  reflexivity.
Qed.
