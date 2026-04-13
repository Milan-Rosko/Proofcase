(*P001_98_01B_Expansion.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / P001_98_01B_Expansion                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  At the next stage of our reasoning, we replace the short divisibility
  witness by one longer proposition whose content is expressed as a single
  sentence with multiple conjunctive clauses.

*)

From P001 Require Export P001_00_Premises.

(*
│
│          We expand `PROPOSITIO` to one (awkwardly) long FOL
│          statement: every integer in `1` through `2n` factors as a
│          power of `2` times an odd integer, the odd integers in that
│          interval are exhausted by a list of length `n`, selecting
│          `n+1` bounded distinct integers forces two selected
│          integers to share an odd core, and any such shared odd core
│          gives a divisibility orientation.
│
*)

Definition first_expansion : Prop :=
  forall n A,
    (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->
    NoDup A ->
    length A = n + 1 ->
    (forall x,
       1 <= x ->
       x <= 2 * n ->
       exists k m,
         x = 2 ^ k * m /\
         Nat.Odd m) /\
    (exists odd_domain : list nat,
       NoDup odd_domain /\
       length odd_domain = n /\
       forall m,
         In m odd_domain <->
         1 <= m /\ m <= 2 * n /\ Nat.Odd m) /\
    (exists y z m i j,
       In y A /\
       In z A /\
       y <> z /\
       1 <= m /\
       m <= 2 * n /\
       Nat.Odd m /\
       y = 2 ^ i * m /\
       z = 2 ^ j * m) /\
    (forall y z m i j,
       In y A ->
       In z A ->
       y <> z ->
       1 <= m ->
       m <= 2 * n ->
       Nat.Odd m ->
       y = 2 ^ i * m ->
       z = 2 ^ j * m ->
       Nat.divide y z \/ Nat.divide z y).

(*
│
│          The expanded sentence is stronger than the original
│          witness, as the final conjunct already furnishes the
│          divisibility orientation for the colliding pair produced by
│          the previous conjunct.
│
*)

Lemma first_expansion_conserves_WITNESS :
  first_expansion ->
  WITNESS.
Proof.
  intros Hexp.
  intros n A Hbounds Hnodup Hlen.
  destruct (Hexp n A Hbounds Hnodup Hlen) as
      [_ [_
          [[y [z [m [i [j [Hy [Hz [Hneq [Hm_pos [Hm_bound [Hm_odd [Hy_eq Hz_eq]]]]]]]]]]]]
           Horient]]].
  exists y, z.
  repeat split; try assumption.
  exact (Horient y z m i j Hy Hz Hneq Hm_pos Hm_bound Hm_odd Hy_eq Hz_eq).
Qed.

(*
│
│          We keep the long expanded sentence above while the witness
│          is still postulated at the present stage.
│
*)

Conjecture UNCONDITIONAL_PROOF : WITNESS.
