(*L003_02__Certification_Dichotomy.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / L003_02__Certification_Dichotomy                 │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Projection turns a sound and complete verifier into an evaluator, so
  Certification Ascent follows from Evaluator Ascent. At every datum the
  diagonal sentence `g_v` is equivalent to the non-acceptance of the
  duplicated datum, by the formation laws alone; at the quotation of `g_v`
  this is the certification fixed point, for every verifier, with no
  soundness, completeness, level, or decidability premise. The Certification
  Dichotomy is exactly decidability of acceptance at that one claim, and it
  cannot be proved without such a premise: the dichotomy for complete
  verifiers is equivalent to excluded middle.

*)

From L003 Require Export L003_01__Diagonal_Ascent.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            PROJECTION AND ASCENT                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Projection identifies its truth on a claim with acceptance;
│          soundness and completeness identify acceptance with truth.
│
*)

Lemma projection_evaluates :
  forall (C : CertificationStructure) v n,
    SoundFor C v n ->
    CompleteFor C v n ->
    Evaluates C (cs_proj C v) n.
Proof.
  intros C v n Hsound Hcomplete e He x.
  rewrite (cs_proj_sem C v (ds_pair C (ds_code C e) x)).
  split.
  - intro HA.
    exact (Hsound e He x HA).
  - intro Htrue.
    exact (Hcomplete e He x Htrue).
Qed.

Theorem certification_ascent :
  forall (C : CertificationStructure) v n,
    SoundFor C v n ->
    CompleteFor C v n ->
    n < ds_level C v + cs_proj_cost C + ds_dup_cost C + ds_neg_cost C.
Proof.
  intros C v n Hsound Hcomplete.
  pose proof
    (evaluator_ascent C (cs_proj C v) n
       (projection_evaluates C v n Hsound Hcomplete)).
  pose proof (cs_proj_level C v).
  lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               SELF-APPLICATION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Duplication turns the quotation of `g_v` into the pair of
│          two copies; negation negates the projected acceptance
│          claim.
│
*)

Lemma self_application :
  forall (C : CertificationStructure) v,
    DiagonalClaim C v <->
    ~ ds_sem C (cs_proj C v)
        (ds_pair C
          (ds_code C (diagonal_sentence C v))
          (ds_code C (diagonal_sentence C v))).
Proof.
  intros C v.
  unfold DiagonalClaim, diagonal_sentence at 1.
  apply diagonal_of_sem.
Qed.

(*
│
│          Coding-free identity: at every datum `x`, the diagonal
│          sentence holds exactly when no witness makes `v` hold of
│          the pair `<<x, x>, wit w>`. The proof uses only the
│          negation, duplication, and projection laws; no property of
│          quotation enters.
│
*)

Theorem coding_free_identity :
  forall (C : CertificationStructure) v x,
    ds_sem C (diagonal_sentence C v) x <->
    ~ exists w, ds_sem C v (ds_pair C (ds_pair C x x) (cs_wit C w)).
Proof.
  intros C v x.
  unfold diagonal_sentence.
  rewrite diagonal_of_sem, cs_proj_sem.
  reflexivity.
Qed.

(*
│
│          Certification fixed point: the coding-free identity at the
│          quotation of `g_v`. Read through the input convention of
│          certification, the diagonal claim holds exactly when its
│          own verifier does not accept it. Intuitionistic,
│          unconditional.
│
*)

Theorem certification_fixed_point :
  forall (C : CertificationStructure) v,
    DiagonalClaim C v <-> ~ DiagonalAccepted C v.
Proof.
  intros C v.
  exact (coding_free_identity C v (ds_code C (diagonal_sentence C v))).
Qed.

(*
│
│          No verifier is correct at its own diagonal claim.
│
*)

Corollary not_correct_at_diagonal :
  forall (C : CertificationStructure) v,
    ~ (DiagonalAccepted C v <-> DiagonalClaim C v).
Proof.
  intros C v Hcorrect.
  apply (not_iff_own_negation (DiagonalAccepted C v)).
  rewrite Hcorrect at 1.
  apply certification_fixed_point.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           CERTIFICATION DICHOTOMY                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The dichotomy holds for a verifier exactly when acceptance
│          of its diagonal claim is decided. The split is on
│          acceptance; the fixed point supplies the other half of each
│          branch.
│
*)

Theorem certification_dichotomy :
  forall (C : CertificationStructure) v,
    (DiagonalAccepted C v \/ ~ DiagonalAccepted C v) <->
    CertificationFailsAtDiagonal C v.
Proof.
  intros C v.
  pose proof (certification_fixed_point C v) as Hfixed.
  unfold CertificationFailsAtDiagonal.
  split.
  - intros [HA | HnA].
    + left.
      split; [exact HA |].
      intro Hclaim.
      exact (proj1 Hfixed Hclaim HA).
    + right.
      split; [exact HnA |].
      exact (proj2 Hfixed HnA).
  - intros [[HA _] | [HnA _]].
    + left. exact HA.
    + right. exact HnA.
Qed.

(*
│
│          The two branches are disjoint, so at most one holds.
│
*)

Theorem certification_dichotomy_exclusive :
  forall (C : CertificationStructure) v,
    ~ ((DiagonalAccepted C v /\ ~ DiagonalClaim C v) /\
       (~ DiagonalAccepted C v /\ DiagonalClaim C v)).
Proof.
  intros C v [[HA _] [HnA _]].
  exact (HnA HA).
Qed.

(*
│
│          Decidable semantics, in particular Boolean semantics,
│          decides acceptance through projection, so every verifier
│          then satisfies the dichotomy.
│
*)

Corollary decidable_certification_dichotomy :
  forall (C : CertificationStructure),
    DecidableSemantics C ->
    forall v,
      CertificationFailsAtDiagonal C v.
Proof.
  intros C Hdec v.
  apply certification_dichotomy.
  set (c := ds_code C (diagonal_sentence C v)).
  pose proof (cs_proj_sem C v (ds_pair C c c)) as Hproj.
  unfold DiagonalAccepted, Accepts, certification_claim.
  fold c.
  destruct (Hdec (cs_proj C v) (ds_pair C c c)) as [Hp | Hnp].
  - left. exact (proj1 Hproj Hp).
  - right. intro HA. exact (Hnp (proj2 Hproj HA)).
Qed.

(*
│
│          Boolean semantics, reflected by a Boolean evaluation
│          function, is decidable. The Boolean dichotomy of the graded
│          setting is therefore a corollary.
│
*)

Definition BooleanSemantics
    (D : DiagonalStructure) : Prop :=
  exists b : ds_expr D -> ds_data D -> bool,
    forall e x, ds_sem D e x <-> b e x = true.

Lemma boolean_semantics_decidable :
  forall D : DiagonalStructure,
    BooleanSemantics D ->
    DecidableSemantics D.
Proof.
  intros D [b Hb] e x.
  destruct (b e x) eqn:Hbool.
  - left. apply Hb. exact Hbool.
  - right. intro H. apply Hb in H. congruence.
Qed.

Corollary boolean_certification_dichotomy :
  forall C : CertificationStructure,
    BooleanSemantics C ->
    forall v, CertificationFailsAtDiagonal C v.
Proof.
  intros C Hb.
  apply decidable_certification_dichotomy.
  exact (boolean_semantics_decidable C Hb).
Qed.

(*
│
│          Soundness at this single claim leaves the claim true and
│          uncertified. No decidability is needed.
│
*)

Corollary sound_at_diagonal_leaves_true_uncertified :
  forall (C : CertificationStructure) v,
    (DiagonalAccepted C v -> DiagonalClaim C v) ->
    ~ DiagonalAccepted C v /\ DiagonalClaim C v.
Proof.
  intros C v Hsound.
  pose proof (certification_fixed_point C v) as Hfixed.
  assert (HnA : ~ DiagonalAccepted C v).
  { intro HA. exact (proj1 Hfixed (Hsound HA) HA). }
  exact (conj HnA (proj2 Hfixed HnA)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                  SHARPNESS                                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A one-point structure over an arbitrary proposition `Q`.
│          Its base expression means `Q \/ ~ Q`; negation is negation,
│          and duplication and projection are transparent. All levels
│          and costs are zero.
│
*)

Inductive SharpExpr : Type :=
| SBase : SharpExpr
| SNeg : SharpExpr -> SharpExpr
| SDup : SharpExpr -> SharpExpr
| SProj : SharpExpr -> SharpExpr.

Fixpoint sharp_sem (Q : Prop) (e : SharpExpr) : Prop :=
  match e with
  | SBase => Q \/ ~ Q
  | SNeg s => ~ sharp_sem Q s
  | SDup s => sharp_sem Q s
  | SProj s => sharp_sem Q s
  end.

Definition sharp_diagonal (Q : Prop) : DiagonalStructure.
Proof.
  refine
    {| ds_expr := SharpExpr;
       ds_data := unit;
       ds_sem := fun e _ => sharp_sem Q e;
       ds_code := fun _ => tt;
       ds_pair := fun _ _ => tt;
       ds_level := fun _ => 0;
       ds_neg := SNeg;
       ds_dup := SDup;
       ds_neg_cost := 0;
       ds_dup_cost := 0 |};
    intros; cbn; first [tauto | lia].
Defined.

Definition sharp_structure (Q : Prop) : CertificationStructure.
Proof.
  refine
    {| cs_base := sharp_diagonal Q;
       cs_witness := unit;
       cs_wit := fun _ => tt;
       cs_proj := SProj;
       cs_proj_cost := 0 |}.
  - intros e z.
    cbn.
    split.
    + intro H. exists tt. exact H.
    + intros [_ H]. exact H.
  - intros e. cbn. lia.
Defined.

(*
│
│          In the sharp structure the base verifier accepts its
│          diagonal claim exactly when `Q \/ ~ Q`. That claim is
│          refutable, so the verifier is complete at it.
│
*)

Lemma sharp_accepted :
  forall Q : Prop,
    DiagonalAccepted (sharp_structure Q) SBase <-> (Q \/ ~ Q).
Proof.
  intro Q.
  split.
  - intros [w H]. exact H.
  - intro H. exists tt. exact H.
Qed.

Lemma sharp_complete :
  forall Q : Prop,
    DiagonalClaim (sharp_structure Q) SBase ->
    DiagonalAccepted (sharp_structure Q) SBase.
Proof.
  intros Q Hclaim.
  exfalso.
  pose proof (proj1 (certification_fixed_point (sharp_structure Q) SBase) Hclaim)
    as HnA.
  apply HnA.
  apply sharp_accepted.
  right.
  intro HQ.
  apply HnA.
  apply sharp_accepted.
  left.
  exact HQ.
Qed.

(*
│
│          Sharpness: the dichotomy for every verifier complete at its
│          own diagonal claim is equivalent to excluded middle. The
│          decidability premise of `certification_dichotomy` therefore
│          cannot be removed intuitionistically, even under
│          completeness.
│
*)

Theorem dichotomy_sharpness :
  (forall (C : CertificationStructure) v,
     (DiagonalClaim C v -> DiagonalAccepted C v) ->
     CertificationFailsAtDiagonal C v) <->
  (forall Q : Prop, Q \/ ~ Q).
Proof.
  split.
  - intros Hdich Q.
    destruct (Hdich (sharp_structure Q) SBase (sharp_complete Q))
      as [[HA _] | [HnA _]].
    + exact (proj1 (sharp_accepted Q) HA).
    + exfalso.
      apply HnA.
      apply sharp_accepted.
      right.
      intro HQ.
      apply HnA.
      apply sharp_accepted.
      left.
      exact HQ.
  - intros Hlem C v _.
    apply certification_dichotomy.
    apply Hlem.
Qed.
