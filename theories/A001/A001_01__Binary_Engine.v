(*A001_01__Binary_Engine.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / A001_01__Binary_Engine                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Computation-oriented binary engine for A001 carryless pairing. We provide
  fast-doubling Fibonacci arithmetic, a binary greedy Zeckendorf extractor,
  the `IsZeckendorf` specification predicate, and `nat` wrappers for
  executable use. Agreement with the certified unary encoder and decoder is
  established later at the bridge boundary.

*)

From A001 Require Export A001_00_Premises.
Local Open Scope N_scope.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                              FAST FIBONACCI                             │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `fib_fast_pos` computes the adjacent Fibonacci pair for a
│          positive binary index by fast doubling, with the recursion
│          mirroring the binary shape of the input.
│
*)

(*                    fib_fast_pos(p) = (F(p), F(p + 1)).                     *)

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

(*
│
│          `fibN` is the binary-engine Fibonacci function on `N`: zero
│          at index `0`, and fast doubling at positive indices.
│
*)

Definition fibN (n : N) : N :=
  match n with
  | 0 => 0
  | Npos p => fst (fib_fast_pos p)
  end.

(*
│
│          `sum_fibN` evaluates a finite binary support as the sum of
│          its Fibonacci values.
│
*)

(*                 sum_fibN([i₁, …, iₙ]) = F(i₁) + ⋯ + F(iₙ).                 *)

Fixpoint sum_fibN (xs : list N) : N :=
  match xs with
  | [] => 0
  | k :: xs' => fibN k + sum_fibN xs'
  end.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                           ZECKENDORF SUPPORTS                           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A support is strictly decreasing when each listed index
│          exceeds the one that follows it.
│
*)

Fixpoint strictly_decreasingN (xs : list N) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: _ => a > b /\ strictly_decreasingN xs'
      end
  end.

(*
│
│          A support has no adjacent Fibonacci indices when
│          consecutive listed indices differ by at least 2.
│
*)

Fixpoint no_adjacentN (xs : list N) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: _ => a >= b + 2 /\ no_adjacentN xs'
      end
  end.

(*
│
│          Every support index is at least `2`, which excludes the
│          duplicated low Fibonacci value.
│
*)

Fixpoint all_ge_2N (xs : list N) : Prop :=
  match xs with
  | [] => True
  | a :: xs' => 2 <= a /\ all_ge_2N xs'
  end.

(*
│
│          `zeck_validN` packages the three admissibility conditions
│          for binary-engine Zeckendorf supports.
│
*)

(*                 zeck_validN(xs) ≔ strictly_decreasingN(xs)                 *)
(*                    ∧ no_adjacentN(xs) ∧ all_ge_2N(xs).                     *)

Definition zeck_validN (xs : list N) : Prop :=
  strictly_decreasingN xs /\ no_adjacentN xs /\ all_ge_2N xs.

(*
│
│          `IsZeckendorf` states the logical notion of a valid
│          Zeckendorf support, independently of the concrete greedy
│          extractor, and records that the listed Fibonacci indices
│          evaluate to the represented number.
│
*)

(*         IsZeckendorf(n, xs) ⇒ zeck_validN(xs) ∧ sum_fibN(xs) = n.          *)

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

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                            GREEDY EXTRACTION                            │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `search_boundN` is a bit-length-based fuel bound for the
│          binary search loop used to locate a Fibonacci index below
│          the input.
│
*)

Definition search_boundN (x : N) : N :=
  2 * N.size x + 2.

(*
│
│          `max_fib_index_le_loop` searches downward from `k` until it
│          locates a Fibonacci index whose value is at most `x`. We
│          pass explicit fuel to keep the recursion structural.
│
*)

Fixpoint max_fib_index_le_loop (fuel : nat) (x k : N) : N :=
  match fuel with
  | O => 1
  | S fuel' =>
      if k <=? 1 then 1
      else if fibN k <=? x then k
      else max_fib_index_le_loop fuel' x (k - 1)
  end.

(*
│
│          `max_fib_index_leN` starts the downward search from the
│          bit-length-derived bound.
│
*)

Definition max_fib_index_leN (x : N) : N :=
  let k0 := search_boundN x in
  max_fib_index_le_loop (N.to_nat k0) x k0.

(*
│
│          `r0N` is the successor cutoff above the largest Fibonacci
│          index selected by the search.
│
*)

(*                     r0N(x) = max_fib_index_leN(x) + 1.                     *)

Definition r0N (x : N) : N :=
  N.succ (max_fib_index_leN x).

(*
│
│          `zeck_extract_loop` greedily subtracts Fibonacci values
│          from the remainder while forbidding adjacent selected
│          indices.
│
*)

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

(*
│
│          `Z0N` is the binary greedy Zeckendorf support extractor.
│
*)

Definition Z0N (x : N) : list N :=
  let k0 := max_fib_index_leN x in
  zeck_extract_loop (N.to_nat (k0 + 1)) x k0 [].

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                              PAIRING ENGINE                             │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `boundaryN` places the odd support band strictly above the
│          even support band determined by the left input.
│
*)

(*                         boundaryN(x) ≔ 2 · r0N(x).                         *)

Definition boundaryN (x : N) : N :=
  2 * r0N x.

(*
│
│          `even_bandN` embeds the left support by doubling every
│          selected Fibonacci index.
│
*)

(*                    even_bandN(x) ≔ { 2e ∣ e ∈ Z0N(x) }.                    *)

Definition even_bandN (x : N) : list N :=
  map (fun e => 2 * e) (Z0N x).

(*
│
│          `odd_bandN` embeds the right support above the boundary
│          using the affine odd-index map.
│
*)

(*        odd_bandN(x, y) ≔ { boundaryN(x) + (2j − 1) ∣ j ∈ Z0N(y) }.         *)

Definition odd_bandN (x y : N) : list N :=
  map (fun j => boundaryN x + (2 * j - 1)) (Z0N y).

(*
│
│          `pairN` evaluates the disjoint odd and even bands as one
│          Fibonacci support.
│
*)

(*            pairN(x, y) ≔ Σ_F(even_bandN(x) ⧺ odd_bandN(x, y)).             *)

Definition pairN (x y : N) : N :=
  sum_fibN (odd_bandN x y ++ even_bandN x).

(*
│
│          `half_even_indicesN` recovers candidate left-support
│          indices from the even part of a decoded support.
│
*)

Definition half_even_indicesN (zn : list N) : list N :=
  map N.div2 (filter N.even zn).

(*
│
│          `odd_ge_B1N` recognizes odd indices that lie above the
│          boundary and therefore belong to the right band.
│
*)

(*                odd_ge_B1N(B, k) = true ⇔ 2 ∤ k ∧ B + 1 ≤ k.                *)

Definition odd_ge_B1N (Bx k : N) : bool :=
  N.odd k && ((Bx + 1) <=? k).

(*
│
│          `decode_odd_indexN` transports an odd-band index back to
│          its original right-support index.
│
*)

(*                decode_odd_indexN(B, k) ≔ ⌊(k − B + 1) / 2⌋.                *)

Definition decode_odd_indexN (Bx k : N) : N :=
  N.div2 (N.succ (k - Bx)).

(*
│
│          `y_indicesN` extracts and decodes the right-support
│          candidates from a full support.
│
*)

Definition y_indicesN (Bx : N) (zn : list N) : list N :=
  map (decode_odd_indexN Bx) (filter (odd_ge_B1N Bx) zn).

(*
│
│          `unpairN` decodes a code by first rebuilding the left
│          support and then, from its induced boundary, rebuilding the
│          right support.
│
*)

Definition unpairN (n : N) : N * N :=
  let zn := Z0N n in
  let x := sum_fibN (half_even_indicesN zn) in
  let y := sum_fibN (y_indicesN (boundaryN x) zn) in
  (x, y).

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                               NAT WRAPPERS                              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `fib_fast_nat` exposes `fibN` at the ordinary `nat` type.
│
*)

Definition fib_fast_nat (n : nat) : nat :=
  N.to_nat (fibN (N.of_nat n)).

(*
│
│          `Z0_fast_nat` exposes the binary greedy support extractor
│          at the ordinary `nat` type.
│
*)

Definition Z0_fast_nat (x : nat) : list nat :=
  map N.to_nat (Z0N (N.of_nat x)).

(*
│
│          `encode_fast_nat` exposes the binary pairing function at
│          the ordinary `nat` type.
│
*)

Definition encode_fast_nat (a b : nat) : nat :=
  N.to_nat (pairN (N.of_nat a) (N.of_nat b)).

(*
│
│          `decode_fast_nat` exposes the binary unpairing function at
│          the ordinary `nat` type.
│
*)

Definition decode_fast_nat (c : nat) : nat * nat :=
  let '(a, b) := unpairN (N.of_nat c) in
  (N.to_nat a, N.to_nat b).
