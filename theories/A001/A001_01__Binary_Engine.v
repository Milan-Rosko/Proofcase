(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[The present construction introduces a computation-oriented binary engine for the A001 carryless pairing substrate. It keeps the existing proof-facing `nat` development untouched, but provides fast-doubling Fibonacci arithmetic, a binary greedy Zeckendorf extractor, a clean specification predicate, and `nat` bridge wrappers for future extraction and migration work. At the zero boundary, we intentionally leave open how the bridge should be identified with the `nat`-level cutoff / pairing surface over `N+0`; the unary development remains the authoritative proof-facing definition there.]]@*)

(*@head.end@*)

From Stdlib Require Export Arith PeanoNat Bool Lia List Ring ZArith Extraction.
Export ListNotations.
Global Open Scope list_scope.
Local Open Scope N_scope.

(*@inline@[[`fib_fast_pos` computes `(F(p), F(p+1))` by fast doubling over the binary shape of a positive index. The recursion depth is logarithmic in the index, unlike the original unary descent.]]@*)

Fixpoint fib_fast_pos (p : positive) : N * N :=
  match p with
  | xH => (1, 1)
  | xO p' =>
      let '(a, b) := fib_fast_pos p' in
      let a2 := a * a in
      let b2 := b * b in
      let ab2 := 2 * a * b in
      (ab2 - a2, a2 + b2)
  | xI p' =>
      let '(a, b) := fib_fast_pos p' in
      let a2 := a * a in
      let b2 := b * b in
      let ab2 := 2 * a * b in
      (a2 + b2, ab2 + b2)
  end.

Definition fibN (n : N) : N :=
  match n with
  | 0 => 0
  | Npos p => fst (fib_fast_pos p)
  end.

Fixpoint sum_fibN (xs : list N) : N :=
  match xs with
  | [] => 0
  | k :: xs' => fibN k + sum_fibN xs'
  end.

Fixpoint strictly_decreasingN (xs : list N) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: _ => a > b /\ strictly_decreasingN xs'
      end
  end.

Fixpoint no_adjacentN (xs : list N) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: _ => a >= b + 2 /\ no_adjacentN xs'
      end
  end.

Fixpoint all_ge_2N (xs : list N) : Prop :=
  match xs with
  | [] => True
  | a :: xs' => 2 <= a /\ all_ge_2N xs'
  end.

Definition zeck_validN (xs : list N) : Prop :=
  strictly_decreasingN xs /\ no_adjacentN xs /\ all_ge_2N xs.

(*@inline@[[`IsZeckendorf` decouples the logical notion of a valid support from the concrete greedy extractor. Downstream proofs can reason by inversion on this predicate without unfolding the executable search engine.]]@*)

Inductive IsZeckendorf : N -> list N -> Prop :=
| Z_Empty :
    IsZeckendorf 0 []
| Z_Single :
    forall k,
      2 <= k ->
      IsZeckendorf (fibN k) [k]
| Z_Cons :
    forall k head xs n,
      IsZeckendorf n (head :: xs) ->
      head + 2 <= k ->
      fibN k + n < fibN (k + 1) ->
      IsZeckendorf (fibN k + n) (k :: head :: xs).

Theorem IsZeckendorf_sound :
  forall n xs,
    IsZeckendorf n xs ->
    sum_fibN xs = n.
Proof.
  intros n xs Hz.
  induction Hz.
  - reflexivity.
  - simpl. now rewrite N.add_0_r.
  - change (fibN k + sum_fibN (head :: xs) = fibN k + n).
    now rewrite IHHz.
Qed.

(*@inline@[[`search_boundN` is a bit-length based computational bound for the binary search surface. It is deliberately small compared with the unary `x`-sized fuel used by the original engine, and can later be tightened by a proved upper-bound lemma without changing the executable interface.]]@*)

Definition search_boundN (x : N) : N :=
  2 * N.size x + 2.

Fixpoint max_fib_index_le_loop (fuel : nat) (x k : N) : N :=
  match fuel with
  | O => 1
  | S fuel' =>
      if k <=? 1 then 1
      else if fibN k <=? x then k
      else max_fib_index_le_loop fuel' x (k - 1)
  end.

Definition max_fib_index_leN (x : N) : N :=
  let k0 := search_boundN x in
  max_fib_index_le_loop (N.to_nat k0) x k0.

Definition r0N (x : N) : N :=
  N.succ (max_fib_index_leN x).

Fixpoint zeck_extract_loop (fuel : nat) (rem k : N) (acc : list N) : list N :=
  match fuel with
  | O => rev acc
  | S fuel' =>
      if rem =? 0 then rev acc
      else if k <=? 1 then rev acc
      else if fibN k <=? rem then
             zeck_extract_loop fuel' (rem - fibN k) (k - 2) (k :: acc)
           else
             zeck_extract_loop fuel' rem (k - 1) acc
  end.

Definition Z0N (x : N) : list N :=
  let k0 := max_fib_index_leN x in
  zeck_extract_loop (N.to_nat (k0 + 1)) x k0 [].

Definition boundaryN (x : N) : N :=
  2 * r0N x.

Definition even_bandN (x : N) : list N :=
  map (fun e => 2 * e) (Z0N x).

Definition odd_bandN (x y : N) : list N :=
  map (fun j => boundaryN x + (2 * j - 1)) (Z0N y).

Definition pairN (x y : N) : N :=
  sum_fibN (odd_bandN x y ++ even_bandN x).

Definition half_even_indicesN (zn : list N) : list N :=
  map N.div2 (filter N.even zn).

Definition odd_ge_B1N (Bx k : N) : bool :=
  N.odd k && ((Bx + 1) <=? k).

Definition decode_odd_indexN (Bx k : N) : N :=
  N.div2 (N.succ (k - Bx)).

Definition y_indicesN (Bx : N) (zn : list N) : list N :=
  map (decode_odd_indexN Bx) (filter (odd_ge_B1N Bx) zn).

Definition unpairN (n : N) : N * N :=
  let zn := Z0N n in
  let x := sum_fibN (half_even_indicesN zn) in
  let y := sum_fibN (y_indicesN (boundaryN x) zn) in
  (x, y).

(*@inline@[[The following wrappers provide a `nat`-shaped computational bridge into the binary engine. They are intended for extraction and benchmarking, not as replacements for the existing proof-facing definitions; in particular, the identification of the bridge with the unary surface at the zero boundary is deliberately left open over `N+0`.]]@*)

Definition fib_fast_nat (n : nat) : nat :=
  N.to_nat (fibN (N.of_nat n)).

Definition Z0_fast_nat (x : nat) : list nat :=
  map N.to_nat (Z0N (N.of_nat x)).

Definition encode_fast_nat (a b : nat) : nat :=
  N.to_nat (pairN (N.of_nat a) (N.of_nat b)).

Definition decode_fast_nat (c : nat) : nat * nat :=
  let '(a, b) := unpairN (N.of_nat c) in
  (N.to_nat a, N.to_nat b).
