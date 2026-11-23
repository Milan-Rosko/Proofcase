(*L003_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / L003_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Primitive vocabulary for L003. A diagonal structure carries expressions,
  data, proposition-valued semantics, quotation, pairing, levels, and the two
  formation operations negation and duplication. A certification structure
  adds witnesses and existential projection. A size-free language is a
  certification structure without levels; the two layers share one semantics.
  A provability calculus carries sentences, implication, falsity, a box
  operator, and a provability predicate.

  Every law used by a later theorem is either a field of one of these records
  or an explicit premise of that theorem. Quotation carries no law at all: it
  need not be injective, computable, or related to any decoder.

*)

(*
│
│          `Arith_base` and `Lia` supply level arithmetic. `Bool.Bool`
│          supplies the truth-table classifier and the Boolean Lawvere
│          corollary.
│
*)

From Stdlib Require Export Arith_base.
From Stdlib Require Export Lia.
From Stdlib Require Export Bool.Bool.

(*
│
│          `Setoid` allows rewriting with propositional equivalences.
│
*)

From Stdlib Require Export Setoid.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               LAWVERE PATTERN                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A map `f : A -> A -> Y` is point-surjective when every
│          column function `A -> Y` occurs as a row `f a`. Row
│          agreement is pointwise, so no function extensionality is
│          required.
│
*)

Definition PointSurjective
    {A Y : Type}
    (f : A -> A -> Y) : Prop :=
  forall h : A -> Y,
    exists a : A,
      forall x : A,
        f a x = h x.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              DIAGONAL STRUCTURE                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A diagonal structure is the graded setting of the paper.
│          Semantics is proposition-valued and need not be decidable.
│          Negation and duplication have exact semantic laws and
│          additive level costs. Pairing and quotation are bare
│          operations.
│
*)

Record DiagonalStructure : Type := {
  ds_expr : Type;
  ds_data : Type;
  ds_sem : ds_expr -> ds_data -> Prop;
  ds_code : ds_expr -> ds_data;
  ds_pair : ds_data -> ds_data -> ds_data;
  ds_level : ds_expr -> nat;
  ds_neg : ds_expr -> ds_expr;
  ds_dup : ds_expr -> ds_expr;
  ds_neg_cost : nat;
  ds_dup_cost : nat;

  ds_neg_sem :
    forall e x,
      ds_sem (ds_neg e) x <-> ~ ds_sem e x;

  ds_dup_sem :
    forall e y,
      ds_sem (ds_dup e) y <-> ds_sem e (ds_pair y y);

  ds_neg_level :
    forall e,
      ds_level (ds_neg e) <= ds_level e + ds_neg_cost;

  ds_dup_level :
    forall e,
      ds_level (ds_dup e) <= ds_level e + ds_dup_cost
}.

(*
│
│          `u` evaluates level `n` when, on the quotation of every
│          expression of level at most `n`, it reproduces that
│          expression's verdict on every input.
│
*)

Definition Evaluates
    (D : DiagonalStructure)
    (u : ds_expr D)
    (n : nat) : Prop :=
  forall e,
    ds_level D e <= n ->
    forall x,
      ds_sem D u (ds_pair D (ds_code D e) x) <-> ds_sem D e x.

(*
│
│          The escaping row `d_u` is obtained from `u` by duplication
│          followed by negation.
│
*)

Definition diagonal_of
    (D : DiagonalStructure)
    (u : ds_expr D) : ds_expr D :=
  ds_neg D (ds_dup D u).

(*
│
│          A level is diagonal-closed when the escaping row of each of
│          its expressions stays inside it.
│
*)

Definition DiagonalClosed
    (D : DiagonalStructure)
    (n : nat) : Prop :=
  forall e,
    ds_level D e <= n ->
    ds_level D (diagonal_of D e) <= n.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           CERTIFICATION STRUCTURE                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A certification structure adds a witness type, a witness
│          encoding, and existential projection with an additive level
│          cost. Projection is an unrestricted existential; it
│          supplies no witness-search procedure.
│
*)

Record CertificationStructure : Type := {
  cs_base :> DiagonalStructure;
  cs_witness : Type;
  cs_wit : cs_witness -> ds_data cs_base;
  cs_proj : ds_expr cs_base -> ds_expr cs_base;
  cs_proj_cost : nat;

  cs_proj_sem :
    forall e z,
      ds_sem cs_base (cs_proj e) z <->
      exists w,
        ds_sem cs_base e (ds_pair cs_base z (cs_wit w));

  cs_proj_level :
    forall e,
      ds_level cs_base (cs_proj e) <=
      ds_level cs_base e + cs_proj_cost
}.

(*
│
│          The datum presented to a verifier: the claim `(e, x)`
│          paired with the encoded witness `w`.
│
*)

Definition certification_claim
    (C : CertificationStructure)
    (e : ds_expr C)
    (x : ds_data C)
    (w : cs_witness C) : ds_data C :=
  ds_pair C (ds_pair C (ds_code C e) x) (cs_wit C w).

(*
│
│          `Accepts C v e x` means that some witness makes `v` output
│          `true` on the claim that `e` holds of `x`. It is
│          acceptance, not truth.
│
*)

Definition Accepts
    (C : CertificationStructure)
    (v e : ds_expr C)
    (x : ds_data C) : Prop :=
  exists w,
    ds_sem C v (certification_claim C e x w).

(*
│
│          Soundness and completeness are relative to a level bound.
│
*)

Definition SoundFor
    (C : CertificationStructure)
    (v : ds_expr C)
    (n : nat) : Prop :=
  forall e,
    ds_level C e <= n ->
    forall x,
      Accepts C v e x ->
      ds_sem C e x.

Definition CompleteFor
    (C : CertificationStructure)
    (v : ds_expr C)
    (n : nat) : Prop :=
  forall e,
    ds_level C e <= n ->
    forall x,
      ds_sem C e x ->
      Accepts C v e x.

(*
│
│          The diagonal sentence `g_v = neg (dup (proj v))` is built
│          from `v` by three explicit formation rules. No fixed-point
│          principle is assumed.
│
*)

Definition diagonal_sentence
    (C : CertificationStructure)
    (v : ds_expr C) : ds_expr C :=
  diagonal_of C (cs_proj C v).

(*
│
│          The diagonal claim: `g_v` holds of its own quotation.
│
*)

Definition DiagonalClaim
    (C : CertificationStructure)
    (v : ds_expr C) : Prop :=
  ds_sem C (diagonal_sentence C v) (ds_code C (diagonal_sentence C v)).

(*
│
│          Acceptance of the diagonal claim by its own verifier.
│
*)

Definition DiagonalAccepted
    (C : CertificationStructure)
    (v : ds_expr C) : Prop :=
  Accepts C v (diagonal_sentence C v) (ds_code C (diagonal_sentence C v)).

(*
│
│          Certification failure at the diagonal claim is the
│          disjunction of the two branches of the dichotomy: a false
│          claim accepted, or a true claim left uncertified.
│
*)

Definition CertificationFailsAtDiagonal
    (C : CertificationStructure)
    (v : ds_expr C) : Prop :=
  (DiagonalAccepted C v /\ ~ DiagonalClaim C v) \/
  (~ DiagonalAccepted C v /\ DiagonalClaim C v).

(*
│
│          Semantics is decidable when every claim holds or fails.
│          Boolean semantics is the motivating instance; the concrete
│          layer is not decidable.
│
*)

Definition DecidableSemantics
    (D : DiagonalStructure) : Prop :=
  forall e x,
    ds_sem D e x \/ ~ ds_sem D e x.

(*
│
│          Costs are exact when negation, duplication, and projection
│          add their costs exactly rather than at most. The
│          serialization grading of the concrete language has exact
│          costs.
│
*)

Definition ExactCosts
    (C : CertificationStructure) : Prop :=
  (forall e, ds_level C (ds_neg C e) = ds_level C e + ds_neg_cost C) /\
  (forall e, ds_level C (ds_dup C e) = ds_level C e + ds_dup_cost C) /\
  (forall e, ds_level C (cs_proj C e) = ds_level C e + cs_proj_cost C).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           FAITHFUL INTERPRETATION                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A faithful interpretation commutes with negation,
│          duplication, projection, and quotation, and preserves
│          semantics up to equivalence. It is not required to preserve
│          levels, pairing, or witnesses.
│
*)

Record FaithfulInterpretation
    (C D : CertificationStructure) : Type := {
  fi_expr : ds_expr C -> ds_expr D;
  fi_data : ds_data C -> ds_data D;

  fi_neg :
    forall e,
      fi_expr (ds_neg C e) = ds_neg D (fi_expr e);

  fi_dup :
    forall e,
      fi_expr (ds_dup C e) = ds_dup D (fi_expr e);

  fi_proj :
    forall e,
      fi_expr (cs_proj C e) = cs_proj D (fi_expr e);

  fi_code :
    forall e,
      fi_data (ds_code C e) = ds_code D (fi_expr e);

  fi_sem :
    forall e x,
      ds_sem D (fi_expr e) (fi_data x) <-> ds_sem C e x
}.

Arguments fi_expr {C D} _ _.
Arguments fi_data {C D} _ _.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              SIZE-FREE LANGUAGE                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A size-free language has proposition-valued semantics, no
│          levels, and witnesses of any type. Projection is an
│          unrestricted existential and need not be decidable.
│
*)

Record SizeFreeLanguage : Type := {
  sf_expr : Type;
  sf_data : Type;
  sf_witness : Type;
  sf_sem : sf_expr -> sf_data -> Prop;
  sf_code : sf_expr -> sf_data;
  sf_pair : sf_data -> sf_data -> sf_data;
  sf_wit : sf_witness -> sf_data;
  sf_neg : sf_expr -> sf_expr;
  sf_dup : sf_expr -> sf_expr;
  sf_proj : sf_expr -> sf_expr;

  sf_neg_sem :
    forall e x,
      sf_sem (sf_neg e) x <-> ~ sf_sem e x;

  sf_dup_sem :
    forall e y,
      sf_sem (sf_dup e) y <-> sf_sem e (sf_pair y y);

  sf_proj_sem :
    forall e z,
      sf_sem (sf_proj e) z <->
      exists w, sf_sem e (sf_pair z (sf_wit w))
}.

Definition SizeFreeAccepts
    (R : SizeFreeLanguage)
    (v e : sf_expr R)
    (x : sf_data R) : Prop :=
  exists w,
    sf_sem R v (sf_pair R (sf_pair R (sf_code R e) x) (sf_wit R w)).

Definition size_free_diagonal_sentence
    (R : SizeFreeLanguage)
    (v : sf_expr R) : sf_expr R :=
  sf_neg R (sf_dup R (sf_proj R v)).

Definition SizeFreeDiagonalClaim
    (R : SizeFreeLanguage)
    (v : sf_expr R) : Prop :=
  sf_sem R
    (size_free_diagonal_sentence R v)
    (sf_code R (size_free_diagonal_sentence R v)).

Definition SizeFreeDiagonalAccepted
    (R : SizeFreeLanguage)
    (v : sf_expr R) : Prop :=
  SizeFreeAccepts R v
    (size_free_diagonal_sentence R v)
    (sf_code R (size_free_diagonal_sentence R v)).

(*
│
│          The size-free counterpart of a faithful interpretation.
│          Semantic preservation is an equivalence of propositions.
│
*)

Record SizeFreeInterpretation
    (R T : SizeFreeLanguage) : Type := {
  sfi_expr : sf_expr R -> sf_expr T;
  sfi_data : sf_data R -> sf_data T;

  sfi_neg :
    forall e,
      sfi_expr (sf_neg R e) = sf_neg T (sfi_expr e);

  sfi_dup :
    forall e,
      sfi_expr (sf_dup R e) = sf_dup T (sfi_expr e);

  sfi_proj :
    forall e,
      sfi_expr (sf_proj R e) = sf_proj T (sfi_expr e);

  sfi_code :
    forall e,
      sfi_data (sf_code R e) = sf_code T (sfi_expr e);

  sfi_sem :
    forall e x,
      sf_sem T (sfi_expr e) (sfi_data x) <-> sf_sem R e x
}.

Arguments sfi_expr {R T} _ _.
Arguments sfi_data {R T} _ _.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            BOUNDED CERTIFICATION                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A bounded certification family assigns to each level `n` a
│          verifier sound and complete for every expression of level
│          at most `n`. The abstract theorems take it as a hypothesis;
│          the concrete layer constructs one.
│
*)

Definition BoundedCertificationFamily
    (C : CertificationStructure)
    (V : nat -> ds_expr C) : Prop :=
  forall n,
    SoundFor C (V n) n /\ CompleteFor C (V n) n.

(*
│
│          The ascent sequence: `n_0` is given and `n_(k+1)` is the
│          level of the diagonal sentence of `V n_k`.
│
*)

Fixpoint ascent_levels
    (C : CertificationStructure)
    (V : nat -> ds_expr C)
    (n0 k : nat) : nat :=
  match k with
  | O => n0
  | S k' => ds_level C (diagonal_sentence C (V (ascent_levels C V n0 k')))
  end.

(*
│
│          Certification is predicative at `n` when the certified
│          domain is bounded by `n` and excludes the certifier's own
│          diagonal sentence; it is impredicatively closed when the
│          same domain is required to contain that sentence.
│
*)

Definition PredicativeAt
    (C : CertificationStructure)
    (v : ds_expr C)
    (n : nat) : Prop :=
  SoundFor C v n /\
  CompleteFor C v n /\
  n < ds_level C (diagonal_sentence C v).

Definition ImpredicativelyClosed
    (C : CertificationStructure)
    (v : ds_expr C)
    (n : nat) : Prop :=
  SoundFor C v n /\
  CompleteFor C v n /\
  ds_level C (diagonal_sentence C v) <= n.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             PROVABILITY CALCULUS                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A provability calculus is bare syntax plus a provability
│          predicate. Its Hilbert laws and derivability conditions are
│          separate records, so each theorem names exactly the laws it
│          uses.
│
*)

Record ProvabilityCalculus : Type := {
  pc_sent : Type;
  pc_imp : pc_sent -> pc_sent -> pc_sent;
  pc_bot : pc_sent;
  pc_box : pc_sent -> pc_sent;
  pc_prov : pc_sent -> Prop
}.

Definition pc_neg
    (P : ProvabilityCalculus)
    (a : pc_sent P) : pc_sent P :=
  pc_imp P a (pc_bot P).

(*
│
│          Modus ponens and the implicational K and S schemas. No
│          classical axiom is included.
│
*)

Record HilbertKS
    (P : ProvabilityCalculus) : Prop := {
  hks_mp :
    forall a b,
      pc_prov P (pc_imp P a b) ->
      pc_prov P a ->
      pc_prov P b;

  hks_k :
    forall a b,
      pc_prov P (pc_imp P a (pc_imp P b a));

  hks_s :
    forall a b c,
      pc_prov P
        (pc_imp P
          (pc_imp P a (pc_imp P b c))
          (pc_imp P (pc_imp P a b) (pc_imp P a c)))
}.

(*
│
│          The Hilbert-Bernays derivability conditions D1-D3.
│
*)

Record DerivabilityConditions
    (P : ProvabilityCalculus) : Prop := {
  dc_d1 :
    forall a,
      pc_prov P a ->
      pc_prov P (pc_box P a);

  dc_d2 :
    forall a b,
      pc_prov P
        (pc_imp P
          (pc_box P (pc_imp P a b))
          (pc_imp P (pc_box P a) (pc_box P b)));

  dc_d3 :
    forall a,
      pc_prov P (pc_imp P (pc_box P a) (pc_box P (pc_box P a)))
}.

Arguments hks_mp {P} _ _ _ _ _.
Arguments hks_k {P} _ _ _.
Arguments hks_s {P} _ _ _ _.
Arguments dc_d1 {P} _ _ _.
Arguments dc_d2 {P} _ _ _.
Arguments dc_d3 {P} _ _.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              LANGUAGE CALCULUS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A language calculus places the diagonal formation
│          operations inside a provability calculus. Atomic sentences
│          are claims `atom e x`; sentences have a quotation `scode`.
│
*)

Record LanguageCalculus : Type := {
  lc_calc :> ProvabilityCalculus;
  lc_expr : Type;
  lc_data : Type;
  lc_code : lc_expr -> lc_data;
  lc_pair : lc_data -> lc_data -> lc_data;
  lc_neg : lc_expr -> lc_expr;
  lc_dup : lc_expr -> lc_expr;
  lc_proj : lc_expr -> lc_expr;
  lc_verifier : lc_expr;
  lc_atom : lc_expr -> lc_data -> pc_sent lc_calc;
  lc_scode : pc_sent lc_calc -> lc_data
}.

(*
│
│          Box representation: the box of a sentence is, by
│          definition, the atomic claim that the projected verifier
│          holds of its quotation, and atomic sentences are quoted as
│          pairs.
│
*)

Record LanguageBoxRepresentation
    (Lc : LanguageCalculus) : Prop := {
  lbr_scode_atom :
    forall e x,
      lc_scode Lc (lc_atom Lc e x) = lc_pair Lc (lc_code Lc e) x;

  lbr_box_def :
    forall phi,
      pc_box Lc phi =
      lc_atom Lc (lc_proj Lc (lc_verifier Lc)) (lc_scode Lc phi)
}.

(*
│
│          The calculus certifies both directions of the computation
│          rules for negation and duplication. No rule for projection
│          is required.
│
*)

Record CertifiedNegDupRules
    (Lc : LanguageCalculus) : Prop := {
  cndr_neg_out :
    forall e x,
      pc_prov Lc
        (pc_imp Lc (lc_atom Lc (lc_neg Lc e) x)
                   (pc_neg Lc (lc_atom Lc e x)));

  cndr_neg_in :
    forall e x,
      pc_prov Lc
        (pc_imp Lc (pc_neg Lc (lc_atom Lc e x))
                   (lc_atom Lc (lc_neg Lc e) x));

  cndr_dup_out :
    forall e y,
      pc_prov Lc
        (pc_imp Lc (lc_atom Lc (lc_dup Lc e) y)
                   (lc_atom Lc e (lc_pair Lc y y)));

  cndr_dup_in :
    forall e y,
      pc_prov Lc
        (pc_imp Lc (lc_atom Lc e (lc_pair Lc y y))
                   (lc_atom Lc (lc_dup Lc e) y))
}.

(*
│
│          The language-level diagonal sentence `G_v = atom (g_v)
│          (code g_v)`, with `g_v = neg (dup (proj verifier))`.
│
*)

Definition language_diagonal_expr
    (Lc : LanguageCalculus) : lc_expr Lc :=
  lc_neg Lc (lc_dup Lc (lc_proj Lc (lc_verifier Lc))).

Definition language_diagonal_sentence
    (Lc : LanguageCalculus) : pc_sent Lc :=
  lc_atom Lc
    (language_diagonal_expr Lc)
    (lc_code Lc (language_diagonal_expr Lc)).
