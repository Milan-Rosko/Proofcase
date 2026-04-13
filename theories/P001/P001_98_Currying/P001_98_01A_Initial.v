(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[At the present “template” stage, we assume that we can prove our original statement (`PROPOSITION`).]]@*)

(*@head.end@*)

From P001 Require Export P001_00_Premises.

(*@inline@[[We assume by conjecture: We can prove by `UNCONDITIONAL_PROOF` that “Among any collection of n+1 pairwise distinct integers chosen from the integers 1 through 2n, there must exist at least two distinct members of that collection such that one of them divides the other“ follows from `WITNESS`.]]@*)

Conjecture UNCONDITIONAL_PROOF : WITNESS.
