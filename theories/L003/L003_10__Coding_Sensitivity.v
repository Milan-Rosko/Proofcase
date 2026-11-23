(*L003_10__Coding_Sensitivity.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                   Proofcase / L003_10__Coding_Sensitivity                    │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  The obstruction is invariant under recoding; the branch is not. For every
  quotation map whatsoever, the concrete language with that quotation is a
  certification structure, and its diagonal claim is equivalent to its own
  non-acceptance. For the one-node verifier `TBit 0` the branch is fixed by
  the first bit of the quotation of `g_v`, so the standard quotation and its
  bitwise negation, both injective, put it in opposite branches.

  This does not conflict with faithful invariance. A faithful interpretation
  commutes with quotation; no interpretation that is the identity on terms
  carries the standard quotation to its negation while preserving semantics.

*)

From L003 Require Export L003_09__Tseitin_CNF.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                ANY QUOTATION                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A quotation is any map from terms to streams. Nothing is
│          assumed of it.
│
*)

Definition Quotation : Type := ConcreteTerm -> BitStream.

Definition quoted_diagonal (O : Oracle) (q : Quotation) : DiagonalStructure.
Proof.
  refine
    {| ds_expr := ConcreteTerm;
       ds_data := BitStream;
       ds_sem := term_sem O;
       ds_code := q;
       ds_pair := stream_pair;
       ds_level := term_level;
       ds_neg := TNot;
       ds_dup := TDup;
       ds_neg_cost := 3;
       ds_dup_cost := 3 |}.
  - intros e x. reflexivity.
  - intros e y. reflexivity.
  - intro e. rewrite (proj1 (term_level_tag e)). lia.
  - intro e. rewrite (proj1 (proj2 (term_level_tag e))). lia.
Defined.

Definition quoted_structure (O : Oracle) (q : Quotation) : CertificationStructure.
Proof.
  refine
    {| cs_base := quoted_diagonal O q;
       cs_witness := BitStream;
       cs_wit := fun w => w;
       cs_proj := TProj;
       cs_proj_cost := 3 |}.
  - intros e z. reflexivity.
  - intro e.
    change (term_level (TProj e) <= term_level e + 3).
    rewrite (proj2 (proj2 (term_level_tag e))).
    lia.
Defined.

(*
│
│          The diagonal claim and its acceptance under the quotation
│          `q`.
│
*)

Definition QuotedClaim (O : Oracle) (q : Quotation) (v : ConcreteTerm) : Prop :=
  term_sem O (diagonal_term v) (q (diagonal_term v)).

Definition QuotedAccepted (O : Oracle) (q : Quotation) (v : ConcreteTerm) : Prop :=
  exists w : BitStream,
    term_sem O v
      (stream_pair (stream_pair (q (diagonal_term v)) (q (diagonal_term v))) w).

Lemma quoted_diagonal_is_abstract :
  forall O q v,
    (QuotedClaim O q v <-> DiagonalClaim (quoted_structure O q) v) /\
    (QuotedAccepted O q v <-> DiagonalAccepted (quoted_structure O q) v).
Proof.
  intros O q v.
  split; reflexivity.
Qed.

Lemma standard_quotation :
  forall O v,
    (QuotedClaim O term_code v <-> ConcreteDiagonalClaim O v) /\
    (QuotedAccepted O term_code v <-> ConcreteAccepted O v).
Proof.
  intros O v.
  split; reflexivity.
Qed.

(*
│
│          Robust obstruction: under every quotation, the diagonal
│          claim is equivalent to its own non-acceptance.
│
*)

Theorem dichotomy_any_quotation :
  forall O (q : Quotation) v,
    QuotedClaim O q v <-> ~ QuotedAccepted O q v.
Proof.
  intros O q v.
  exact (certification_fixed_point (quoted_structure O q) v).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 BRANCH FLIP                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The negated quotation flips every bit of the standard one.
│
*)

Definition neg_code (t : ConcreteTerm) : BitStream :=
  fun i => negb (term_code t i).

(*
│
│          Both quotations are injective up to pointwise equality of
│          streams.
│
*)

Lemma term_code_injective :
  forall e e',
    (forall i, term_code e i = term_code e' i) ->
    e = e'.
Proof.
  intros e e' H.
  symmetry.
  apply code_match_unique.
  intros i _.
  exact (H i).
Qed.

Lemma neg_code_injective :
  forall e e',
    (forall i, neg_code e i = neg_code e' i) ->
    e = e'.
Proof.
  intros e e' H.
  apply term_code_injective.
  intro i.
  pose proof (H i) as Hi.
  unfold neg_code in Hi.
  destruct (term_code e i), (term_code e' i); simpl in Hi;
    congruence.
Qed.

(*
│
│          `TBit 0` reads the first bit of the quotation of `g_v`, the
│          first bit of the negation tag. Under the standard quotation
│          that bit is `false`, so the claim is true and uncertified;
│          under the negated quotation it is `true`, so the claim is
│          accepted and false. The flip holds relative to every
│          oracle.
│
*)

Theorem branch_depends_on_quotation :
  forall O,
    (~ QuotedAccepted O term_code (TBit 0) /\ QuotedClaim O term_code (TBit 0)) /\
    (QuotedAccepted O neg_code (TBit 0) /\ ~ QuotedClaim O neg_code (TBit 0)).
Proof.
  intro O.
  assert (Hstd : ~ QuotedAccepted O term_code (TBit 0)).
  { intros [w Hw]. cbn in Hw. discriminate Hw. }
  assert (Hneg : QuotedAccepted O neg_code (TBit 0)).
  { exists (fun _ => false). reflexivity. }
  split.
  - split; [exact Hstd |].
    exact (proj2 (dichotomy_any_quotation O term_code (TBit 0)) Hstd).
  - split; [exact Hneg |].
    intro Hclaim.
    exact (proj1 (dichotomy_any_quotation O neg_code (TBit 0)) Hclaim Hneg).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           RECODING IS NOT FAITHFUL                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          No faithful interpretation from the standard quotation to
│          the negated one is the identity on terms: commuting with
│          quotation and preserving the meaning of `TBit 0` would make
│          some bit equal to its own negation.
│
*)

Theorem recoding_not_faithful :
  forall O (I : FaithfulInterpretation (quoted_structure O term_code)
                                       (quoted_structure O neg_code)),
    ~ (forall e, fi_expr I e = e).
Proof.
  intros O I Hid.
  set (x := term_code (TConst true)).
  pose proof (fi_code _ _ I (TConst true)) as Hcode.
  pose proof (fi_sem _ _ I (TBit 0) x) as Hsem.
  change (term_sem O (fi_expr I (TBit 0)) (fi_data I x) <->
          term_sem O (TBit 0) x) in Hsem.
  rewrite (Hid (TBit 0)) in Hsem.
  change (fi_data I x = neg_code (fi_expr I (TConst true))) in Hcode.
  rewrite (Hid (TConst true)) in Hcode.
  rewrite Hcode in Hsem.
  cbn in Hsem.
  destruct Hsem as [Hto _].
  discriminate (Hto eq_refl).
Qed.
