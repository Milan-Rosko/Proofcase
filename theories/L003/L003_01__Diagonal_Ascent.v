(*L003_01__Diagonal_Ascent.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / L003_01__Diagonal_Ascent                     │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Lawvere's fixed-point pattern at the level of types, and its graded,
  language-internal realization: diagonal escape, Evaluator Ascent, and the
  absence of an internal total classifier. All results are pointwise in the
  supplied structure.

*)

From L003 Require Export L003_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               LAWVERE PATTERN                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A point-surjective `f : A -> A -> Y` gives every endomap of
│          `Y` a fixed point: represent `x |-> t (f x x)` by a row `a`
│          and evaluate it at `a`.
│
*)

Theorem lawvere_fixed_point :
  forall (A Y : Type) (f : A -> A -> Y),
    PointSurjective f ->
    forall t : Y -> Y,
      exists y : Y, t y = y.
Proof.
  intros A Y f Hf t.
  destruct (Hf (fun x => t (f x x))) as [a Ha].
  exists (f a a).
  symmetry.
  exact (Ha a).
Qed.

(*
│
│          Boolean negation has no fixed point, so no map into `A ->
│          bool` is point-surjective.
│
*)

Theorem no_point_surjection_to_bool :
  forall (A : Type) (f : A -> A -> bool),
    ~ PointSurjective f.
Proof.
  intros A f Hf.
  destruct (lawvere_fixed_point A bool f Hf negb) as [y Hy].
  destruct y; discriminate Hy.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               DIAGONAL ESCAPE                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The escaping row negates `u` on duplicated input, and its
│          level exceeds that of `u` by at most the two formation
│          costs.
│
*)

Lemma diagonal_of_sem :
  forall (D : DiagonalStructure) u y,
    ds_sem D (diagonal_of D u) y <-> ~ ds_sem D u (ds_pair D y y).
Proof.
  intros D u y.
  unfold diagonal_of.
  rewrite ds_neg_sem, ds_dup_sem.
  reflexivity.
Qed.

Lemma diagonal_of_level :
  forall (D : DiagonalStructure) u,
    ds_level D (diagonal_of D u) <=
    ds_level D u + ds_dup_cost D + ds_neg_cost D.
Proof.
  intros D u.
  unfold diagonal_of.
  pose proof (ds_neg_level D (ds_dup D u)).
  pose proof (ds_dup_level D u).
  lia.
Qed.

(*
│
│          No proposition is equivalent to its own negation. This is
│          the intuitionistic core of every diagonal argument below.
│
*)

Lemma not_iff_own_negation :
  forall P : Prop, ~ (P <-> ~ P).
Proof.
  intros P [Hto Hfrom].
  assert (Hn : ~ P).
  { intro HP. exact (Hto HP HP). }
  exact (Hn (Hfrom Hn)).
Qed.

(*
│
│          On the quotation of its own escaping row, `u` and `d_u`
│          disagree.
│
*)

Theorem diagonal_escape :
  forall (D : DiagonalStructure) u,
    ~ (ds_sem D u
         (ds_pair D (ds_code D (diagonal_of D u)) (ds_code D (diagonal_of D u)))
       <-> ds_sem D (diagonal_of D u) (ds_code D (diagonal_of D u))).
Proof.
  intros D u.
  rewrite diagonal_of_sem.
  apply not_iff_own_negation.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               EVALUATOR ASCENT                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An evaluator of level `n` lies strictly above `n` minus the
│          cost of diagonal formation. Otherwise its own escaping row
│          would be inside the evaluated level.
│
*)

Theorem evaluator_ascent :
  forall (D : DiagonalStructure) u n,
    Evaluates D u n ->
    n < ds_level D u + ds_dup_cost D + ds_neg_cost D.
Proof.
  intros D u n Hev.
  destruct (Nat.lt_ge_cases n (ds_level D u + ds_dup_cost D + ds_neg_cost D))
    as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
    pose proof (diagonal_of_level D u) as Hlevel.
    apply (diagonal_escape D u).
    apply Hev.
    lia.
Qed.

(*
│
│          No single expression evaluates every level.
│
*)

Corollary no_universal_evaluator :
  forall D : DiagonalStructure,
    ~ exists u, forall n, Evaluates D u n.
Proof.
  intros D [u Hu].
  pose proof
    (evaluator_ascent D u _
       (Hu (ds_level D u + ds_dup_cost D + ds_neg_cost D))).
  lia.
Qed.

(*
│
│          Local form: a diagonal-closed level contains no evaluator
│          of itself.
│
*)

Corollary closed_level_has_no_internal_evaluator :
  forall (D : DiagonalStructure) n,
    DiagonalClosed D n ->
    forall u,
      ds_level D u <= n ->
      ~ Evaluates D u n.
Proof.
  intros D n Hclosed u Hu Hev.
  apply (diagonal_escape D u).
  apply Hev.
  apply Hclosed.
  exact Hu.
Qed.

(*
│
│          A meta-level rule producing an evaluator for each level has
│          outputs of unbounded level. The rule is not one bounded
│          object of the language.
│
*)

Corollary evaluator_rule_unbounded :
  forall (D : DiagonalStructure) (B : nat -> ds_expr D),
    (forall n, Evaluates D (B n) n) ->
    forall m,
      m < ds_level D (B (m + (ds_dup_cost D + ds_neg_cost D))).
Proof.
  intros D B HB m.
  pose proof
    (evaluator_ascent D _ _ (HB (m + (ds_dup_cost D + ds_neg_cost D)))).
  lia.
Qed.

(*
│
│          When negation and duplication strictly raise levels, as
│          they do under any size grading, a diagonal-closed level
│          contains no expression at all. The local statements above
│          are then vacuous, and the unconditional bound of
│          `evaluator_ascent` is the operative one.
│
*)

Lemma diagonal_closed_level_empty :
  forall (D : DiagonalStructure) n,
    (forall e, ds_level D e < ds_level D (ds_neg D e)) ->
    (forall e, ds_level D e < ds_level D (ds_dup D e)) ->
    DiagonalClosed D n ->
    forall e, n < ds_level D e.
Proof.
  intros D n Hneg Hdup Hclosed.
  assert (Hclimb :
    forall k e, ds_level D e <= n -> k <= n -> exists e', k < ds_level D e' /\ ds_level D e' <= n).
  { induction k as [| k IH]; intros e He Hk.
    - exists (diagonal_of D e).
      split.
      + unfold diagonal_of.
        pose proof (Hneg (ds_dup D e)).
        pose proof (Hdup e).
        lia.
      + apply Hclosed. exact He.
    - destruct (IH e He ltac:(lia)) as [e' [Hlt Hle]].
      exists (diagonal_of D e').
      split.
      + unfold diagonal_of.
        pose proof (Hneg (ds_dup D e')).
        pose proof (Hdup e').
        lia.
      + apply Hclosed. exact Hle. }
  intro e.
  destruct (Nat.lt_ge_cases n (ds_level D e)) as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
    destruct (Hclimb n e Hge (le_n n)) as [e' [Hlt Hle]].
    lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         NO INTERNAL TOTAL CLASSIFIER                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Global form: no expression evaluates every expression of
│          the same language on every input. External evaluation is
│          not excluded.
│
*)

Theorem no_internal_total_classifier :
  forall D : DiagonalStructure,
    ~ exists u,
        forall e x,
          ds_sem D u (ds_pair D (ds_code D e) x) <-> ds_sem D e x.
Proof.
  intros D [u Hu].
  apply (diagonal_escape D u).
  apply Hu.
Qed.
