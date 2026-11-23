(*L003_04__Ascent_Hierarchy.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                    Proofcase / L003_04__Ascent_Hierarchy                     │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Bounded certifiers and the ascent hierarchy. A sound and complete certifier
  for level `n` has its diagonal sentence strictly above `n`; impredicative
  closure is therefore impossible unconditionally. Under the hypothesis of a
  bounded certification family, the iterated diagonal levels strictly
  increase within explicit two-sided bounds, each certifier is incorrect at
  its own diagonal claim, the next certifier is correct there, and the
  failure points are pairwise distinct.

*)

From L003 Require Export L003_03__Invariance_Size_Free.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            DIAGONAL BEYOND DOMAIN                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          If the diagonal sentence of a sound and complete certifier
│          lay inside its domain, the certifier would be correct at
│          its own diagonal claim, contradicting
│          `not_correct_at_diagonal`.
│
*)

Lemma diagonal_beyond_domain :
  forall (C : CertificationStructure) v n,
    SoundFor C v n ->
    CompleteFor C v n ->
    n < ds_level C (diagonal_sentence C v).
Proof.
  intros C v n Hsound Hcomplete.
  destruct (Nat.lt_ge_cases n (ds_level C (diagonal_sentence C v)))
    as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
    apply (not_correct_at_diagonal C v).
    split.
    + exact (Hsound _ Hge _).
    + exact (Hcomplete _ Hge _).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             SETTLED ONE LEVEL UP                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Under exact costs the diagonal sentence lies exactly the
│          three formation costs above its verifier.
│
*)

Lemma exact_diagonal_level :
  forall (C : CertificationStructure) v,
    ExactCosts C ->
    ds_level C (diagonal_sentence C v) =
    ds_level C v + cs_proj_cost C + ds_dup_cost C + ds_neg_cost C.
Proof.
  intros C v [Hneg [Hdup Hproj]].
  unfold diagonal_sentence, diagonal_of.
  rewrite Hneg, Hdup, Hproj.
  lia.
Qed.

(*
│
│          Any internal evaluator whose domain contains `g_v` lies
│          strictly above `v` plus the projection cost. This replaces
│          every hypothesis of a diagonal-closed level, which is
│          vacuous whenever formation strictly raises levels.
│
*)

Theorem settler_above_verifier :
  forall (C : CertificationStructure) v B n,
    ExactCosts C ->
    ds_level C (diagonal_sentence C v) <= n ->
    Evaluates C B n ->
    ds_level C v + cs_proj_cost C < ds_level C B.
Proof.
  intros C v B n Hexact Hdomain HB.
  pose proof (exact_diagonal_level C v Hexact).
  pose proof (evaluator_ascent C B n HB).
  lia.
Qed.

(*
│
│          An evaluator whose domain contains `g_v` settles the
│          diagonal claim: on the duplicated quotation it agrees with
│          the claim.
│
*)

Lemma evaluator_settles_diagonal :
  forall (C : CertificationStructure) v B n,
    ds_level C (diagonal_sentence C v) <= n ->
    Evaluates C B n ->
    (ds_sem C B
       (ds_pair C (ds_code C (diagonal_sentence C v))
                  (ds_code C (diagonal_sentence C v))) <->
     DiagonalClaim C v).
Proof.
  intros C v B n Hdomain HB.
  exact (HB _ Hdomain _).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                 PREDICATIVE AND IMPREDICATIVE CERTIFICATION                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Impredicative closure is impossible for every verifier and
│          every level. No bounded family is assumed.
│
*)

Theorem impredicative_closure_impossible :
  forall (C : CertificationStructure) v n,
    ~ ImpredicativelyClosed C v n.
Proof.
  intros C v n [Hsound [Hcomplete Hlevel]].
  pose proof (diagonal_beyond_domain C v n Hsound Hcomplete).
  lia.
Qed.

(*
│
│          Every correct bounded certifier is automatically
│          predicative.
│
*)

Theorem correct_certifier_is_predicative :
  forall (C : CertificationStructure) v n,
    SoundFor C v n ->
    CompleteFor C v n ->
    PredicativeAt C v n.
Proof.
  intros C v n Hsound Hcomplete.
  split; [exact Hsound |].
  split; [exact Hcomplete |].
  exact (diagonal_beyond_domain C v n Hsound Hcomplete).
Qed.

(*
│
│          Conditional half: a bounded family supplies predicative
│          certification at every level.
│
*)

Corollary predicative_certification_exists :
  forall (C : CertificationStructure) (V : nat -> ds_expr C),
    BoundedCertificationFamily C V ->
    forall n, exists v, PredicativeAt C v n.
Proof.
  intros C V HV n.
  exists (V n).
  destruct (HV n) as [Hsound Hcomplete].
  exact (correct_certifier_is_predicative C (V n) n Hsound Hcomplete).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               ASCENT HIERARCHY                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          For each `k`: the levels strictly increase; `V n_k` is not
│          correct at its own diagonal claim; and `V n_(k+1)` is sound
│          and complete at that claim, so its acceptance coincides
│          with truth there. When acceptance of `V n_k` at its claim
│          is decided, the middle conjunct sharpens to the dichotomy
│          through `certification_dichotomy`.
│
*)

Theorem ascent_hierarchy :
  forall (C : CertificationStructure) (V : nat -> ds_expr C) n0,
    BoundedCertificationFamily C V ->
    forall k,
      ascent_levels C V n0 k < ascent_levels C V n0 (S k) /\
      ~ (DiagonalAccepted C (V (ascent_levels C V n0 k)) <->
         DiagonalClaim C (V (ascent_levels C V n0 k))) /\
      (Accepts C (V (ascent_levels C V n0 (S k)))
         (diagonal_sentence C (V (ascent_levels C V n0 k)))
         (ds_code C (diagonal_sentence C (V (ascent_levels C V n0 k))))
       <->
       DiagonalClaim C (V (ascent_levels C V n0 k))).
Proof.
  intros C V n0 HV k.
  set (nk := ascent_levels C V n0 k).
  destruct (HV nk) as [Hsound Hcomplete].
  destruct (HV (ascent_levels C V n0 (S k))) as [Hsound' Hcomplete'].
  assert (Hlevel :
    ds_level C (diagonal_sentence C (V nk)) <= ascent_levels C V n0 (S k)).
  { simpl. fold nk. lia. }
  split.
  - simpl. fold nk.
    exact (diagonal_beyond_domain C (V nk) nk Hsound Hcomplete).
  - split.
    + exact (not_correct_at_diagonal C (V nk)).
    + split.
      * intro HA.
        exact (Hsound' _ Hlevel _ HA).
      * intro Htrue.
        exact (Hcomplete' _ Hlevel _ Htrue).
Qed.

(*
│
│          Two-sided bound: each step of the hierarchy rises by at
│          least one level and by at most the size of the current
│          certifier plus the three formation costs. Hence `n_k` grows
│          at least linearly in `k`.
│
*)

Theorem ascent_hierarchy_bounds :
  forall (C : CertificationStructure) (V : nat -> ds_expr C) n0,
    BoundedCertificationFamily C V ->
    forall k,
      ascent_levels C V n0 k < ascent_levels C V n0 (S k) /\
      ascent_levels C V n0 (S k) <=
        ds_level C (V (ascent_levels C V n0 k)) +
        cs_proj_cost C + ds_dup_cost C + ds_neg_cost C /\
      n0 + k <= ascent_levels C V n0 k.
Proof.
  intros C V n0 HV k.
  split; [exact (proj1 (ascent_hierarchy C V n0 HV k)) |].
  split.
  - simpl.
    unfold diagonal_sentence.
    pose proof (diagonal_of_level C (cs_proj C (V (ascent_levels C V n0 k)))).
    pose proof (cs_proj_level C (V (ascent_levels C V n0 k))).
    lia.
  - induction k as [| k IH].
    + simpl. lia.
    + pose proof (proj1 (ascent_hierarchy C V n0 HV k)).
      lia.
Qed.

Lemma ascent_levels_strictly_increasing :
  forall (C : CertificationStructure) (V : nat -> ds_expr C) n0,
    BoundedCertificationFamily C V ->
    forall i j,
      i < j ->
      ascent_levels C V n0 i < ascent_levels C V n0 j.
Proof.
  intros C V n0 HV i j Hij.
  induction Hij as [| m Him IH].
  - exact (proj1 (ascent_hierarchy C V n0 HV i)).
  - pose proof (proj1 (ascent_hierarchy C V n0 HV m)).
    lia.
Qed.

(*
│
│          Proliferation: the failure points `g (V n_k)` are pairwise
│          distinct, so there are infinitely many of them, generated
│          by the single operation `v |-> g_v`.
│
*)

Corollary proliferation :
  forall (C : CertificationStructure) (V : nat -> ds_expr C) n0,
    BoundedCertificationFamily C V ->
    forall i j,
      diagonal_sentence C (V (ascent_levels C V n0 i)) =
      diagonal_sentence C (V (ascent_levels C V n0 j)) ->
      i = j.
Proof.
  intros C V n0 HV i j Heq.
  assert (Hnext :
    ascent_levels C V n0 (S i) = ascent_levels C V n0 (S j)).
  { simpl. rewrite Heq. reflexivity. }
  destruct (Nat.lt_total i j) as [Hlt | [Hsame | Hgt]].
  - pose proof
      (ascent_levels_strictly_increasing C V n0 HV (S i) (S j)
         (proj1 (Nat.succ_lt_mono i j) Hlt)).
    lia.
  - exact Hsame.
  - pose proof
      (ascent_levels_strictly_increasing C V n0 HV (S j) (S i)
         (proj1 (Nat.succ_lt_mono j i) Hgt)).
    lia.
Qed.
