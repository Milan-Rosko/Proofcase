(*L003_03__Invariance_Size_Free.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / L003_03__Invariance_Size_Free                   │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Faithful interpretations transport the diagonal sentence, its claim, and
  its non-acceptance. Dropping levels gives the size-free fixed point,
  pointwise incompleteness, the internal truth obstruction, and the sharp
  constructive boundary. Forgetting levels and grading trivially move between
  the graded and size-free layers without changing any diagonal notion.

*)

From L003 Require Export L003_02__Certification_Dichotomy.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                  INVARIANCE                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Commutation with the three formation operations maps `g_v`
│          to `g_(tau v)`; commutation with quotation and semantic
│          preservation keep its claim. Non-acceptance is then
│          preserved through the certification fixed point on both
│          sides; no preservation of pairing or witnesses is used.
│          Acceptance itself is preserved whenever it is decided on
│          both sides.
│
*)

Theorem faithful_interpretation_invariance :
  forall (C D : CertificationStructure)
         (I : FaithfulInterpretation C D)
         (v : ds_expr C),
    fi_expr I (diagonal_sentence C v) = diagonal_sentence D (fi_expr I v) /\
    (DiagonalClaim D (fi_expr I v) <-> DiagonalClaim C v) /\
    (~ DiagonalAccepted D (fi_expr I v) <-> ~ DiagonalAccepted C v).
Proof.
  intros C D I v.
  assert (Hsentence :
    fi_expr I (diagonal_sentence C v) = diagonal_sentence D (fi_expr I v)).
  { unfold diagonal_sentence, diagonal_of.
    rewrite (fi_neg C D I), (fi_dup C D I), (fi_proj C D I).
    reflexivity. }
  assert (Hclaim :
    DiagonalClaim D (fi_expr I v) <-> DiagonalClaim C v).
  { unfold DiagonalClaim.
    rewrite <- Hsentence, <- (fi_code C D I).
    apply (fi_sem C D I). }
  split; [exact Hsentence |].
  split; [exact Hclaim |].
  rewrite <- (certification_fixed_point D), <- (certification_fixed_point C).
  exact Hclaim.
Qed.

Corollary faithful_acceptance_invariance :
  forall (C D : CertificationStructure)
         (I : FaithfulInterpretation C D)
         (v : ds_expr C),
    (DiagonalAccepted C v \/ ~ DiagonalAccepted C v) ->
    (DiagonalAccepted D (fi_expr I v) \/ ~ DiagonalAccepted D (fi_expr I v)) ->
    (DiagonalAccepted D (fi_expr I v) <-> DiagonalAccepted C v).
Proof.
  intros C D I v HdecC HdecD.
  destruct (faithful_interpretation_invariance C D I v) as [_ [_ Hneg]].
  split; intro HA.
  - destruct HdecC as [HAC | HnAC]; [exact HAC |].
    exfalso. exact (proj2 Hneg HnAC HA).
  - destruct HdecD as [HAD | HnAD]; [exact HAD |].
    exfalso. exact (proj1 Hneg HnAD HA).
Qed.

(*
│
│          With acceptance decided on both sides, the dichotomy branch
│          is preserved: each branch of the source holds exactly when
│          the same branch of the target holds.
│
*)

Corollary faithful_branch_invariance :
  forall (C D : CertificationStructure)
         (I : FaithfulInterpretation C D)
         (v : ds_expr C),
    (DiagonalAccepted C v \/ ~ DiagonalAccepted C v) ->
    (DiagonalAccepted D (fi_expr I v) \/ ~ DiagonalAccepted D (fi_expr I v)) ->
    ((DiagonalAccepted D (fi_expr I v) /\ ~ DiagonalClaim D (fi_expr I v)) <->
     (DiagonalAccepted C v /\ ~ DiagonalClaim C v)) /\
    ((~ DiagonalAccepted D (fi_expr I v) /\ DiagonalClaim D (fi_expr I v)) <->
     (~ DiagonalAccepted C v /\ DiagonalClaim C v)).
Proof.
  intros C D I v HdecC HdecD.
  destruct (faithful_interpretation_invariance C D I v) as [_ [Hclaim _]].
  pose proof (faithful_acceptance_invariance C D I v HdecC HdecD) as Hacc.
  rewrite Hclaim, Hacc.
  split; reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            SIZE-FREE FIXED POINT                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The coding-free identity in a size-free language: at every
│          datum, by the formation laws alone.
│
*)

Theorem size_free_coding_free_identity :
  forall (R : SizeFreeLanguage) v x,
    sf_sem R (size_free_diagonal_sentence R v) x <->
    ~ exists w, sf_sem R v (sf_pair R (sf_pair R x x) (sf_wit R w)).
Proof.
  intros R v x.
  unfold size_free_diagonal_sentence.
  rewrite sf_neg_sem, sf_dup_sem, sf_proj_sem.
  reflexivity.
Qed.

(*
│
│          At the quotation of the diagonal sentence the identity
│          becomes the size-free fixed point. No decidability, level,
│          or bound is used.
│
*)

Theorem size_free_fixed_point :
  forall (R : SizeFreeLanguage) v,
    SizeFreeDiagonalClaim R v <-> ~ SizeFreeDiagonalAccepted R v.
Proof.
  intros R v.
  exact (size_free_coding_free_identity R v
           (sf_code R (size_free_diagonal_sentence R v))).
Qed.

(*
│
│          Soundness at the diagonal claim makes it true and
│          uncertified.
│
*)

Corollary pointwise_incompleteness :
  forall (R : SizeFreeLanguage) v,
    (SizeFreeDiagonalAccepted R v -> SizeFreeDiagonalClaim R v) ->
    SizeFreeDiagonalClaim R v /\ ~ SizeFreeDiagonalAccepted R v.
Proof.
  intros R v Hsound.
  assert (Hnacc : ~ SizeFreeDiagonalAccepted R v).
  { intro Hacc.
    exact (proj1 (size_free_fixed_point R v) (Hsound Hacc) Hacc). }
  split.
  - exact (proj2 (size_free_fixed_point R v) Hnacc).
  - exact Hnacc.
Qed.

(*
│
│          No verifier is both sound and complete at its own diagonal
│          claim.
│
*)

Corollary not_sound_and_complete_at_diagonal :
  forall (R : SizeFreeLanguage) v,
    (SizeFreeDiagonalAccepted R v -> SizeFreeDiagonalClaim R v) ->
    (SizeFreeDiagonalClaim R v -> SizeFreeDiagonalAccepted R v) ->
    False.
Proof.
  intros R v Hsound Hcomplete.
  destruct (pointwise_incompleteness R v Hsound) as [Hclaim Hnacc].
  exact (Hnacc (Hcomplete Hclaim)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            CONSTRUCTIVE BOUNDARY                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          From `G <-> ~ A` and completeness `G -> A`, intuitionistic
│          logic proves `~ G` and `~ ~ A`; the dichotomy disjunction
│          is equivalent to `A`, and `A` is equivalent to its own
│          decision `A \/ ~ A`. `dichotomy_sharpness` shows that no
│          intuitionistic argument proves the disjunction itself.
│
*)

Theorem constructive_boundary :
  forall G A : Prop,
    (G <-> ~ A) ->
    (G -> A) ->
    (~ G /\ ~ ~ A) /\
    (((A /\ ~ G) \/ (~ A /\ G)) <-> A) /\
    (A <-> (A \/ ~ A)).
Proof.
  intros G A Hfixed Hcomplete.
  assert (HnG : ~ G).
  { intro HG.
    exact (proj1 Hfixed HG (Hcomplete HG)). }
  split.
  - split.
    + exact HnG.
    + intro HnA.
      exact (HnG (proj2 Hfixed HnA)).
  - split.
    + split.
      * intros [[HA _] | [_ HG]].
        -- exact HA.
        -- contradiction.
      * intro HA.
        left.
        exact (conj HA HnG).
    + split.
      * intro HA. left. exact HA.
      * intros [HA | HnA].
        -- exact HA.
        -- exfalso. exact (HnG (proj2 Hfixed HnA)).
Qed.

(*
│
│          The weaker paper form: unsoundness is irrefutable.
│
*)

Corollary constructive_boundary_double_negation :
  forall G A : Prop,
    (G <-> ~ A) ->
    (G -> A) ->
    ~ ~ (A /\ ~ G).
Proof.
  intros G A Hfixed Hcomplete Hno.
  destruct (constructive_boundary G A Hfixed Hcomplete)
    as [[HnG HnnA] _].
  apply HnnA.
  intro HA.
  exact (Hno (conj HA HnG)).
Qed.

(*
│
│          Sharpness schema: if the dichotomy disjunction followed
│          from the fixed point and completeness alone, excluded
│          middle would follow. Take `A := Q \/ ~ Q`, for which
│          completeness holds because `G` is refutable.
│
*)

Theorem sharpness_schema :
  (forall G A : Prop, (G <-> ~ A) -> (G -> A) -> ((A /\ ~ G) \/ (~ A /\ G))) ->
  forall Q : Prop, Q \/ ~ Q.
Proof.
  intros Hschema Q.
  assert (Hnn : ~ ~ (Q \/ ~ Q)).
  { intro Hn. apply Hn. right. intro HQ. apply Hn. left. exact HQ. }
  destruct (Hschema (~ (Q \/ ~ Q)) (Q \/ ~ Q)
              (iff_refl _) (fun HG => False_ind _ (Hnn HG)))
    as [[HA _] | [HnA _]].
  - exact HA.
  - exfalso. exact (Hnn HnA).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          INTERNAL TRUTH OBSTRUCTION                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          No expression of a size-free language is a truth predicate
│          for that language. Its escaping row at its own quotation
│          would be equivalent to its own negation.
│
*)

Theorem internal_truth_obstruction :
  forall R : SizeFreeLanguage,
    ~ exists u,
        forall e x,
          sf_sem R u (sf_pair R (sf_code R e) x) <-> sf_sem R e x.
Proof.
  intros R [u Hu].
  set (d := sf_neg R (sf_dup R u)).
  assert (Hself : sf_sem R d (sf_code R d) <-> ~ sf_sem R d (sf_code R d)).
  { unfold d at 1.
    rewrite (sf_neg_sem R (sf_dup R u)), (sf_dup_sem R u),
      (Hu d (sf_code R d)).
    reflexivity. }
  assert (Hn : ~ sf_sem R d (sf_code R d)).
  { intro Hd.
    exact (proj1 Hself Hd Hd). }
  exact (Hn (proj2 Hself Hn)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             SIZE-FREE INVARIANCE                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A size-free interpretation maps the diagonal sentence to
│          the diagonal sentence and preserves the diagonal claim.
│          Through the fixed point it preserves non-acceptance.
│          Acceptance itself is not claimed: the interpretation is not
│          required to respect pairing or witnesses, and without
│          decidability `~ A <-> ~ B` does not give `A <-> B`.
│
*)

Theorem size_free_interpretation_invariance :
  forall (R T : SizeFreeLanguage)
         (I : SizeFreeInterpretation R T)
         (v : sf_expr R),
    sfi_expr I (size_free_diagonal_sentence R v) =
      size_free_diagonal_sentence T (sfi_expr I v) /\
    (SizeFreeDiagonalClaim T (sfi_expr I v) <-> SizeFreeDiagonalClaim R v) /\
    (~ SizeFreeDiagonalAccepted T (sfi_expr I v) <->
     ~ SizeFreeDiagonalAccepted R v).
Proof.
  intros R T I v.
  assert (Hsentence :
    sfi_expr I (size_free_diagonal_sentence R v) =
    size_free_diagonal_sentence T (sfi_expr I v)).
  { unfold size_free_diagonal_sentence.
    rewrite (sfi_neg R T I), (sfi_dup R T I), (sfi_proj R T I).
    reflexivity. }
  assert (Hclaim :
    SizeFreeDiagonalClaim T (sfi_expr I v) <-> SizeFreeDiagonalClaim R v).
  { unfold SizeFreeDiagonalClaim.
    rewrite <- Hsentence, <- (sfi_code R T I).
    apply (sfi_sem R T I). }
  split; [exact Hsentence |].
  split; [exact Hclaim |].
  rewrite <- (size_free_fixed_point T (sfi_expr I v)),
    <- (size_free_fixed_point R v).
  exact Hclaim.
Qed.

(*
│
│          With acceptance decided on both sides, a size-free
│          interpretation preserves acceptance and therefore the
│          dichotomy branch.
│
*)

Corollary size_free_acceptance_invariance :
  forall (R T : SizeFreeLanguage)
         (I : SizeFreeInterpretation R T)
         (v : sf_expr R),
    (SizeFreeDiagonalAccepted R v \/ ~ SizeFreeDiagonalAccepted R v) ->
    (SizeFreeDiagonalAccepted T (sfi_expr I v) \/
     ~ SizeFreeDiagonalAccepted T (sfi_expr I v)) ->
    (SizeFreeDiagonalAccepted T (sfi_expr I v) <-> SizeFreeDiagonalAccepted R v).
Proof.
  intros R T I v HdecR HdecT.
  destruct (size_free_interpretation_invariance R T I v) as [_ [_ Hneg]].
  split; intro HA.
  - destruct HdecR as [HAR | HnAR]; [exact HAR |].
    exfalso. exact (proj2 Hneg HnAR HA).
  - destruct HdecT as [HAT | HnAT]; [exact HAT |].
    exfalso. exact (proj1 Hneg HnAT HA).
Qed.

Corollary size_free_branch_invariance :
  forall (R T : SizeFreeLanguage)
         (I : SizeFreeInterpretation R T)
         (v : sf_expr R),
    (SizeFreeDiagonalAccepted R v \/ ~ SizeFreeDiagonalAccepted R v) ->
    (SizeFreeDiagonalAccepted T (sfi_expr I v) \/
     ~ SizeFreeDiagonalAccepted T (sfi_expr I v)) ->
    ((SizeFreeDiagonalAccepted T (sfi_expr I v) /\
      ~ SizeFreeDiagonalClaim T (sfi_expr I v)) <->
     (SizeFreeDiagonalAccepted R v /\ ~ SizeFreeDiagonalClaim R v)) /\
    ((~ SizeFreeDiagonalAccepted T (sfi_expr I v) /\
      SizeFreeDiagonalClaim T (sfi_expr I v)) <->
     (~ SizeFreeDiagonalAccepted R v /\ SizeFreeDiagonalClaim R v)).
Proof.
  intros R T I v HdecR HdecT.
  destruct (size_free_interpretation_invariance R T I v) as [_ [Hclaim _]].
  pose proof (size_free_acceptance_invariance R T I v HdecR HdecT) as Hacc.
  rewrite Hclaim, Hacc.
  split; reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          ONE SEMANTICS, TWO LAYERS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Every graded certification structure is a size-free
│          language once its levels are forgotten. The semantics is
│          reused verbatim.
│
*)

Definition forget_levels
    (C : CertificationStructure) : SizeFreeLanguage :=
  {| sf_expr := ds_expr C;
     sf_data := ds_data C;
     sf_witness := cs_witness C;
     sf_sem := ds_sem C;
     sf_code := ds_code C;
     sf_pair := ds_pair C;
     sf_wit := cs_wit C;
     sf_neg := ds_neg C;
     sf_dup := ds_dup C;
     sf_proj := cs_proj C;
     sf_neg_sem := ds_neg_sem C;
     sf_dup_sem := ds_dup_sem C;
     sf_proj_sem := cs_proj_sem C |}.

(*
│
│          Forgetting levels leaves the diagonal sentence, its claim,
│          and its acceptance unchanged.
│
*)

Theorem forget_levels_diagonal :
  forall (C : CertificationStructure) v,
    size_free_diagonal_sentence (forget_levels C) v = diagonal_sentence C v /\
    (SizeFreeDiagonalClaim (forget_levels C) v <-> DiagonalClaim C v) /\
    (SizeFreeDiagonalAccepted (forget_levels C) v <-> DiagonalAccepted C v).
Proof.
  intros C v.
  split; [reflexivity |].
  split; reflexivity.
Qed.

(*
│
│          Conversely, every size-free language is a graded
│          certification structure with all levels and costs zero.
│
*)

Definition trivial_grading_base
    (R : SizeFreeLanguage) : DiagonalStructure :=
  {| ds_expr := sf_expr R;
     ds_data := sf_data R;
     ds_sem := sf_sem R;
     ds_code := sf_code R;
     ds_pair := sf_pair R;
     ds_level := fun _ => 0;
     ds_neg := sf_neg R;
     ds_dup := sf_dup R;
     ds_neg_cost := 0;
     ds_dup_cost := 0;
     ds_neg_sem := sf_neg_sem R;
     ds_dup_sem := sf_dup_sem R;
     ds_neg_level := fun _ => le_n 0;
     ds_dup_level := fun _ => le_n 0 |}.

Definition trivial_grading
    (R : SizeFreeLanguage) : CertificationStructure :=
  {| cs_base := trivial_grading_base R;
     cs_witness := sf_witness R;
     cs_wit := sf_wit R;
     cs_proj := sf_proj R;
     cs_proj_cost := 0;
     cs_proj_sem := sf_proj_sem R;
     cs_proj_level := fun _ => le_n 0 |}.

Theorem trivial_grading_diagonal :
  forall (R : SizeFreeLanguage) v,
    diagonal_sentence (trivial_grading R) v = size_free_diagonal_sentence R v /\
    (DiagonalClaim (trivial_grading R) v <-> SizeFreeDiagonalClaim R v) /\
    (DiagonalAccepted (trivial_grading R) v <-> SizeFreeDiagonalAccepted R v).
Proof.
  intros R v.
  split; [reflexivity |].
  split; reflexivity.
Qed.
