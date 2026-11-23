(*L003_05__Internal_Certification.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / L003_05__Internal_Certification                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Internal certification. Over an abstract provability calculus with modus
  ponens and the implicational K and S schemas, the derivability conditions
  D1-D3 give Löb's theorem and, at `A = bot`, Gödel II. In a language
  calculus that defines box through projection and certifies the negation and
  duplication rules, the diagonal sentence `G_v` is a certified fixed point
  of `~ box`, without D1-D3; Gödel II at the language level then uses D1-D3
  explicitly.

  Each theorem states `HilbertKS` and, where used, `DerivabilityConditions`
  as premises. Nothing here relates `pc_prov` to semantic truth. A Gödel-Löb
  model over the natural numbers shows that these premises, together with a
  fixed point of `~ box` and consistency, are jointly satisfiable.

*)

From L003 Require Export L003_04__Ascent_Hierarchy.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            HILBERT DERIVED RULES                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Section Hilbert.

  Variable P : ProvabilityCalculus.
  Hypothesis HK : HilbertKS P.

  Local Notation "a ==> b" := (pc_imp P a b) (at level 55, right associativity).
  Local Notation "|- a" := (pc_prov P a) (at level 60).

  Lemma hilbert_lift :
    forall c x, |- x -> |- (c ==> x).
  Proof.
    intros c x H.
    exact (hks_mp HK _ _ (hks_k HK x c) H).
  Qed.

  Lemma hilbert_s_rule :
    forall a b c,
      |- (a ==> b ==> c) ->
      |- (a ==> b) ->
      |- (a ==> c).
  Proof.
    intros a b c H1 H2.
    exact (hks_mp HK _ _ (hks_mp HK _ _ (hks_s HK a b c) H1) H2).
  Qed.

  Lemma hilbert_compose :
    forall a b c,
      |- (a ==> b) ->
      |- (b ==> c) ->
      |- (a ==> c).
  Proof.
    intros a b c H1 H2.
    exact (hilbert_s_rule a b c (hilbert_lift a _ H2) H1).
  Qed.

  Lemma hilbert_contraposition :
    forall a b,
      |- (a ==> b) ->
      |- (pc_neg P b ==> pc_neg P a).
  Proof.
    intros a b H.
    unfold pc_neg.
    pose proof (hks_k HK (b ==> pc_bot P) a) as Hk.
    pose proof (hilbert_lift (b ==> pc_bot P) _ (hks_s HK a b (pc_bot P)))
      as Hs.
    pose proof (hilbert_s_rule _ _ _ Hs Hk) as Hstep.
    exact (hilbert_s_rule _ _ _ Hstep (hilbert_lift _ _ H)).
  Qed.

  Hypothesis HD : DerivabilityConditions P.

  Lemma box_monotone :
    forall a b,
      |- (a ==> b) ->
      |- (pc_box P a ==> pc_box P b).
  Proof.
    intros a b H.
    exact (hks_mp HK _ _ (dc_d2 HD a b) (dc_d1 HD _ H)).
  Qed.

  Lemma box_distribute2 :
    forall a b c,
      |- (a ==> b ==> c) ->
      |- (pc_box P a ==> pc_box P b ==> pc_box P c).
  Proof.
    intros a b c H.
    exact (hilbert_compose _ _ _ (box_monotone _ _ H) (dc_d2 HD b c)).
  Qed.

End Hilbert.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               LÖB AND GÖDEL II                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Löb: if both directions of `L <-> (box L -> A)` are
│          certified, certification of `box A -> A` yields
│          certification of `A`.
│
*)

Theorem loeb :
  forall (P : ProvabilityCalculus) (A L : pc_sent P),
    HilbertKS P ->
    DerivabilityConditions P ->
    pc_prov P (pc_imp P L (pc_imp P (pc_box P L) A)) ->
    pc_prov P (pc_imp P (pc_imp P (pc_box P L) A) L) ->
    pc_prov P (pc_imp P (pc_box P A) A) ->
    pc_prov P A.
Proof.
  intros P A L HK HD Hfwd Hbwd Hreflect.
  pose proof (box_distribute2 P HK HD _ _ _ Hfwd) as T1.
  pose proof (hilbert_s_rule P HK _ _ _ T1 (dc_d3 HD L)) as T2.
  pose proof (hilbert_compose P HK _ _ _ T2 Hreflect) as T3.
  pose proof (hks_mp HK _ _ Hbwd T3) as T4.
  exact (hks_mp HK _ _ T3 (dc_d1 HD _ T4)).
Qed.

(*
│
│          Gödel II is Löb at `A = bot`: with a certified fixed point
│          `G <-> ~ box G`, certification of `~ box bot` yields
│          certification of `bot`.
│
*)

Corollary goedel_second :
  forall (P : ProvabilityCalculus) (G : pc_sent P),
    HilbertKS P ->
    DerivabilityConditions P ->
    pc_prov P (pc_imp P G (pc_neg P (pc_box P G))) ->
    pc_prov P (pc_imp P (pc_neg P (pc_box P G)) G) ->
    pc_prov P (pc_neg P (pc_box P (pc_bot P))) ->
    pc_prov P (pc_bot P).
Proof.
  intros P G HK HD Hfwd Hbwd Hcon.
  exact (loeb P (pc_bot P) G HK HD Hfwd Hbwd Hcon).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          LANGUAGE-LEVEL FIXED POINT                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Under box representation, box `G_v` is the atomic claim
│          that the projected verifier holds of the pair of two
│          quotations of `g_v`.
│
*)

Lemma language_box_unfold :
  forall Lc : LanguageCalculus,
    LanguageBoxRepresentation Lc ->
    pc_box Lc (language_diagonal_sentence Lc) =
    lc_atom Lc (lc_proj Lc (lc_verifier Lc))
      (lc_pair Lc
        (lc_code Lc (language_diagonal_expr Lc))
        (lc_code Lc (language_diagonal_expr Lc))).
Proof.
  intros Lc Hrep.
  rewrite (lbr_box_def Lc Hrep).
  unfold language_diagonal_sentence.
  rewrite (lbr_scode_atom Lc Hrep).
  reflexivity.
Qed.

(*
│
│          The verifier certifies both directions of `G_v <-> ~ box
│          G_v`, using only the certified negation and duplication
│          rules and the K/S calculus. D1-D3 are not used.
│
*)

Theorem language_fixed_point :
  forall Lc : LanguageCalculus,
    HilbertKS Lc ->
    LanguageBoxRepresentation Lc ->
    CertifiedNegDupRules Lc ->
    pc_prov Lc
      (pc_imp Lc (language_diagonal_sentence Lc)
                 (pc_neg Lc (pc_box Lc (language_diagonal_sentence Lc)))) /\
    pc_prov Lc
      (pc_imp Lc (pc_neg Lc (pc_box Lc (language_diagonal_sentence Lc)))
                 (language_diagonal_sentence Lc)).
Proof.
  intros Lc HK Hrep Hrules.
  rewrite (language_box_unfold Lc Hrep).
  unfold language_diagonal_sentence, language_diagonal_expr.
  split.
  - eapply (hilbert_compose Lc HK).
    + apply (cndr_neg_out Lc Hrules).
    + apply (hilbert_contraposition Lc HK).
      apply (cndr_dup_in Lc Hrules).
  - eapply (hilbert_compose Lc HK).
    + apply (hilbert_contraposition Lc HK).
      apply (cndr_dup_out Lc Hrules).
    + apply (cndr_neg_in Lc Hrules).
Qed.

(*
│
│          Gödel II at the language level: with D1-D3, certification
│          of `~ box bot` yields certification of `bot`.
│
*)

Corollary language_goedel_second :
  forall Lc : LanguageCalculus,
    HilbertKS Lc ->
    DerivabilityConditions Lc ->
    LanguageBoxRepresentation Lc ->
    CertifiedNegDupRules Lc ->
    pc_prov Lc (pc_neg Lc (pc_box Lc (pc_bot Lc))) ->
    pc_prov Lc (pc_bot Lc).
Proof.
  intros Lc HK HD Hrep Hrules Hcon.
  destruct (language_fixed_point Lc HK Hrep Hrules) as [Hfwd Hbwd].
  exact (goedel_second Lc _ HK HD Hfwd Hbwd Hcon).
Qed.

(*
│
│          A consistent calculus certifies neither `G_v` nor `~ box
│          bot`.
│
*)

Corollary consistent_certifies_neither :
  forall Lc : LanguageCalculus,
    HilbertKS Lc ->
    DerivabilityConditions Lc ->
    LanguageBoxRepresentation Lc ->
    CertifiedNegDupRules Lc ->
    ~ pc_prov Lc (pc_bot Lc) ->
    ~ pc_prov Lc (language_diagonal_sentence Lc) /\
    ~ pc_prov Lc (pc_neg Lc (pc_box Lc (pc_bot Lc))).
Proof.
  intros Lc HK HD Hrep Hrules Hconsistent.
  split.
  - intro HG.
    apply Hconsistent.
    destruct (language_fixed_point Lc HK Hrep Hrules) as [Hfwd _].
    exact (hks_mp HK _ _ (hks_mp HK _ _ Hfwd HG) (dc_d1 HD _ HG)).
  - intro Hcon.
    exact (Hconsistent (language_goedel_second Lc HK HD Hrep Hrules Hcon)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           A MODEL OF THE PREMISES                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Modal formulas, evaluated over the frame of natural numbers
│          in which a world sees exactly the smaller worlds. The frame
│          is transitive, irreflexive, and conversely well-founded, so
│          it is a Gödel-Löb frame; every finite initial segment is a
│          finite strict linear order.
│
*)

Inductive ModalFormula : Type :=
| MAtom : nat -> ModalFormula
| MBot : ModalFormula
| MImp : ModalFormula -> ModalFormula -> ModalFormula
| MBox : ModalFormula -> ModalFormula.

Fixpoint modal_holds
    (V : nat -> nat -> Prop)
    (w : nat)
    (a : ModalFormula) : Prop :=
  match a with
  | MAtom p => V p w
  | MBot => False
  | MImp b c => modal_holds V w b -> modal_holds V w c
  | MBox b => forall v, v < w -> modal_holds V v b
  end.

(*
│
│          Provability is truth at every world under every valuation.
│
*)

Definition gl_calculus : ProvabilityCalculus :=
  {| pc_sent := ModalFormula;
     pc_imp := MImp;
     pc_bot := MBot;
     pc_box := MBox;
     pc_prov := fun a => forall V w, modal_holds V w a |}.

Lemma gl_hilbert : HilbertKS gl_calculus.
Proof.
  split; cbn.
  - intros a b Hab Ha V w. exact (Hab V w (Ha V w)).
  - intros a b V w Ha _. exact Ha.
  - intros a b c V w Habc Hab Ha. exact (Habc Ha (Hab Ha)).
Qed.

Lemma gl_derivability : DerivabilityConditions gl_calculus.
Proof.
  split; cbn.
  - intros a Ha V w v _. exact (Ha V v).
  - intros a b V w Hab Ha v Hv. exact (Hab v Hv (Ha v Hv)).
  - intros a V w Ha v Hv u Hu. apply Ha. lia.
Qed.

Lemma gl_consistent : ~ pc_prov gl_calculus (pc_bot gl_calculus).
Proof.
  intro H.
  exact (H (fun _ _ => False) 0).
Qed.

(*
│
│          Löb's axiom is valid: converse well-foundedness of the
│          frame is strong induction on worlds.
│
*)

Lemma gl_loeb_axiom :
  forall a,
    pc_prov gl_calculus
      (pc_imp gl_calculus
        (pc_box gl_calculus
          (pc_imp gl_calculus (pc_box gl_calculus a) a))
        (pc_box gl_calculus a)).
Proof.
  intros a V w H v.
  induction v as [v IHv] using lt_wf_ind.
  intro Hv.
  apply (H v Hv).
  intros u Hu.
  apply IHv; lia.
Qed.

(*
│
│          The sentence `~ box bot` is a fixed point of `~ box` in the
│          model, so the fixed-point premises of Gödel II are
│          satisfied, not only assumed.
│
*)

Definition gl_fixed_point : ModalFormula :=
  MImp (MBox MBot) MBot.

Lemma gl_fixed_point_forward :
  pc_prov gl_calculus
    (pc_imp gl_calculus gl_fixed_point
      (pc_neg gl_calculus (pc_box gl_calculus gl_fixed_point))).
Proof.
  intros V w HG HB.
  apply HG.
  intro v.
  induction v as [v IHv] using lt_wf_ind.
  intro Hv.
  apply (HB v Hv).
  intros u Hu.
  apply (IHv u Hu).
  lia.
Qed.

Lemma gl_fixed_point_backward :
  pc_prov gl_calculus
    (pc_imp gl_calculus
      (pc_neg gl_calculus (pc_box gl_calculus gl_fixed_point))
      gl_fixed_point).
Proof.
  intros V w HnB H0.
  apply HnB.
  intros v Hv.
  exfalso.
  exact (H0 v Hv).
Qed.

(*
│
│          The premises of `loeb` and `goedel_second` are jointly
│          satisfiable by a consistent calculus with a fixed point of
│          `~ box`. Gödel II then shows that this calculus does not
│          prove its own consistency.
│
*)

Theorem internal_premises_satisfiable :
  exists P : ProvabilityCalculus,
    HilbertKS P /\
    DerivabilityConditions P /\
    ~ pc_prov P (pc_bot P) /\
    (exists G,
       pc_prov P (pc_imp P G (pc_neg P (pc_box P G))) /\
       pc_prov P (pc_imp P (pc_neg P (pc_box P G)) G)) /\
    (forall a,
       pc_prov P (pc_imp P (pc_box P (pc_imp P (pc_box P a) a)) (pc_box P a))) /\
    ~ pc_prov P (pc_neg P (pc_box P (pc_bot P))).
Proof.
  exists gl_calculus.
  split; [exact gl_hilbert |].
  split; [exact gl_derivability |].
  split; [exact gl_consistent |].
  split.
  { exists gl_fixed_point.
    split; [exact gl_fixed_point_forward | exact gl_fixed_point_backward]. }
  split; [exact gl_loeb_axiom |].
  intro Hcon.
  apply gl_consistent.
  exact (goedel_second gl_calculus gl_fixed_point gl_hilbert gl_derivability
           gl_fixed_point_forward gl_fixed_point_backward Hcon).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        A MODEL OF THE LANGUAGE LAYER                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A language calculus whose box is literally the atomic claim
│          of the projected verifier. Sentences are syntax; quotation
│          of an atom is the pair of the quoted expression and its
│          datum, and every other sentence is quoted as itself.
│
*)

Inductive LExpr : Type :=
| LVerifier : LExpr
| LNeg : LExpr -> LExpr
| LDup : LExpr -> LExpr
| LProj : LExpr -> LExpr.

Inductive LSent : Type :=
| SAtom : LExpr -> LData -> LSent
| SBot : LSent
| SImp : LSent -> LSent -> LSent
with LData : Type :=
| DCode : LExpr -> LData
| DPair : LData -> LData -> LData
| DQuote : LSent -> LData.

Definition lscode (phi : LSent) : LData :=
  match phi with
  | SAtom e x => DPair (DCode e) x
  | _ => DQuote phi
  end.

Definition ldecode (d : LData) : LSent :=
  match d with
  | DPair (DCode e) x => SAtom e x
  | DQuote phi => phi
  | _ => SBot
  end.

Lemma ldecode_lscode :
  forall phi, ldecode (lscode phi) = phi.
Proof.
  intro phi.
  destruct phi; reflexivity.
Qed.

(*
│
│          Truth at a world, given the set of sentences boxed there.
│          Negation and duplication follow their computation rules;
│          the projected verifier holds of a datum exactly when the
│          decoded sentence is boxed.
│
*)

Fixpoint latom_sat (B : LSent -> Prop) (e : LExpr) (x : LData) : Prop :=
  match e with
  | LVerifier => False
  | LNeg e' => ~ latom_sat B e' x
  | LDup e' => latom_sat B e' (DPair x x)
  | LProj LVerifier => B (ldecode x)
  | LProj _ => False
  end.

Fixpoint lsat (B : LSent -> Prop) (phi : LSent) : Prop :=
  match phi with
  | SAtom e x => latom_sat B e x
  | SBot => False
  | SImp a b => lsat B a -> lsat B b
  end.

(*
│
│          Worlds are natural numbers seeing the smaller ones. A
│          sentence is boxed at `w` when it holds at every smaller
│          world; the recursion is on worlds, so the circular diagonal
│          sentence is well defined.
│
*)

Fixpoint lboxed (w : nat) (phi : LSent) : Prop :=
  match w with
  | O => True
  | S v => lboxed v phi /\ lsat (lboxed v) phi
  end.

Definition lholds (w : nat) (phi : LSent) : Prop :=
  lsat (lboxed w) phi.

Lemma lboxed_iff :
  forall w phi, lboxed w phi <-> forall v, v < w -> lholds v phi.
Proof.
  induction w as [| w IH]; intro phi; simpl.
  - split; [intros _ v Hv; lia | intros _; exact I].
  - rewrite IH.
    split.
    + intros [Hbelow Hw] v Hv.
      destruct (Nat.eq_dec v w) as [-> | Hne]; [exact Hw |].
      apply Hbelow. lia.
    + intro H.
      split.
      * intros v Hv. apply H. lia.
      * apply H. lia.
Qed.

Definition model_calc : ProvabilityCalculus :=
  {| pc_sent := LSent;
     pc_imp := SImp;
     pc_bot := SBot;
     pc_box := fun phi => SAtom (LProj LVerifier) (lscode phi);
     pc_prov := fun phi => forall w, lholds w phi |}.

Definition model_language : LanguageCalculus :=
  {| lc_calc := model_calc;
     lc_expr := LExpr;
     lc_data := LData;
     lc_code := DCode;
     lc_pair := DPair;
     lc_neg := LNeg;
     lc_dup := LDup;
     lc_proj := LProj;
     lc_verifier := LVerifier;
     lc_atom := SAtom;
     lc_scode := lscode |}.

Lemma model_box_holds :
  forall w phi,
    lholds w (pc_box model_language phi) <-> forall v, v < w -> lholds v phi.
Proof.
  intros w phi.
  change (lboxed w (ldecode (lscode phi)) <-> forall v, v < w -> lholds v phi).
  rewrite ldecode_lscode.
  apply lboxed_iff.
Qed.

Lemma model_hilbert : HilbertKS model_language.
Proof.
  split; cbn; unfold lholds; cbn.
  - intros a b Hab Ha w. exact (Hab w (Ha w)).
  - intros a b w Ha _. exact Ha.
  - intros a b c w Habc Hab Ha. exact (Habc Ha (Hab Ha)).
Qed.

Lemma model_derivability : DerivabilityConditions model_language.
Proof.
  split.
  - intros a Ha w.
    apply model_box_holds.
    intros v _. exact (Ha v).
  - intros a b w Hab Ha.
    apply (proj2 (model_box_holds w b)).
    intros v Hv.
    exact ((proj1 (model_box_holds w (pc_imp model_language a b)) Hab) v Hv
             ((proj1 (model_box_holds w a) Ha) v Hv)).
  - intros a w Ha.
    apply (proj2 (model_box_holds w (pc_box model_language a))).
    intros v Hv.
    apply (proj2 (model_box_holds v a)).
    intros u Hu.
    exact ((proj1 (model_box_holds w a) Ha) u ltac:(lia)).
Qed.

Lemma model_box_representation : LanguageBoxRepresentation model_language.
Proof.
  split; reflexivity.
Qed.

Lemma model_neg_dup_rules : CertifiedNegDupRules model_language.
Proof.
  split; intros e x w; cbn; unfold lholds; cbn; intro H; exact H.
Qed.

Lemma model_consistent : ~ pc_prov model_language (pc_bot model_language).
Proof.
  intro H.
  exact (H 0).
Qed.

(*
│
│          The premises of the language-level fixed point and of
│          language-level Gödel II are jointly satisfiable by a
│          consistent language calculus; it then certifies neither its
│          diagonal sentence nor its own consistency.
│
*)

Theorem language_premises_satisfiable :
  exists Lc : LanguageCalculus,
    HilbertKS Lc /\
    DerivabilityConditions Lc /\
    LanguageBoxRepresentation Lc /\
    CertifiedNegDupRules Lc /\
    ~ pc_prov Lc (pc_bot Lc) /\
    ~ pc_prov Lc (language_diagonal_sentence Lc) /\
    ~ pc_prov Lc (pc_neg Lc (pc_box Lc (pc_bot Lc))).
Proof.
  exists model_language.
  split; [exact model_hilbert |].
  split; [exact model_derivability |].
  split; [exact model_box_representation |].
  split; [exact model_neg_dup_rules |].
  split; [exact model_consistent |].
  exact (consistent_certifies_neither model_language model_hilbert
           model_derivability model_box_representation model_neg_dup_rules
           model_consistent).
Qed.
