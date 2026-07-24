(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Two minimal effectivity witnesses for the normalized CARRYLESS SEQUENT checker. The first checks one K line; the second checks two K lines followed by modus ponens. Both use only inductive formulas, rules, lines, and ordinary lists, so no A001 arithmetic container is materialized.]]@*)

(*@doc.pl@[[These are closed compile-time computations, not an additional theorem layer. General K/S/MP correctness, whole-derivation validity, and target-sensitive verification are supplied by `normalized_stepb_iff`, `normalized_linesb_iff`, and `normalized_verifyb_iff`; the probes only confirm that representative normalized programs reduce immediately.]]@*)

(*@head.end@*)

From A002 Require Import A002_95_API.

(*@section@[[K EFFECTIVITY]]@*)

(*@inline@[[`sanity_A` and `sanity_B` are two distinct normalized propositional variables used to instantiate K.]]@*)

Definition sanity_A : NormalizedFormula :=
  NFVar 0.

Definition sanity_B : NormalizedFormula :=
  NFVar 1.

(*@inline@[[`sanity_K` is the normalized K instance `A → (B → A)`.]]@*)

(*@unicodemath@[[sanity_K ≔ A → (B → A).]]@*)

Definition sanity_K : NormalizedFormula :=
  NFImp sanity_A (NFImp sanity_B sanity_A).

(*@inline@[[The first derivation consists of the single K formula tagged by the normalized K rule.]]@*)

Definition sanity_K_derivation : NormalizedDerivation :=
  [Build_NormalizedLine NRAxK sanity_K].

(*@inline@[[The structural checker accepts the closed K derivation by direct reduction.]]@*)

(*@unicodemath@[[normalized_verifyb([K(A,B)],K(A,B))=true.]]@*)

Example sanity_normalized_K_checks :
  normalized_verifyb sanity_K_derivation sanity_K = true.
Proof.
  reflexivity.
Qed.

(*@section@[[MODUS PONENS EFFECTIVITY]]@*)

(*@inline@[[The MP conclusion is `A → K`; its major premise `K → (A → K)` is itself another K instance.]]@*)

Definition sanity_MP_conclusion : NormalizedFormula :=
  NFImp sanity_A sanity_K.

Definition sanity_MP_major : NormalizedFormula :=
  NFImp sanity_K sanity_MP_conclusion.

(*@inline@[[The second derivation proves `K`, proves `K → (A → K)` by K again, then cites lines `0` and `1` to obtain `A → K` by MP.]]@*)

Definition sanity_MP_derivation : NormalizedDerivation :=
  [ Build_NormalizedLine NRAxK sanity_K;
    Build_NormalizedLine NRAxK sanity_MP_major;
    Build_NormalizedLine (NRMP 0 1) sanity_MP_conclusion ].

(*@inline@[[The normalized checker resolves both prefix citations and accepts the three-line derivation by direct reduction.]]@*)

(*@unicodemath@[[normalized_verifyb([K, K→(A→K), MP(0,1,A→K)], A→K)=true.]]@*)

Example sanity_normalized_MP_checks :
  normalized_verifyb sanity_MP_derivation sanity_MP_conclusion = true.
Proof.
  reflexivity.
Qed.
