(*L003_95_API.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / L003_95_API                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Public API for L003. Each paper result is stated as a named `Prop` contract
  over arbitrary structures. `L003_CORE_CONTRACT` contains the coding-free
  identity, the Certification Dichotomy, the size-free fixed point,
  brute-force evaluation inside the language, and the Solver's Paradox for
  plain SAT. `L003_CONTRACT` contains every contract in proof order.

  Contracts state exactly the premises their proofs use. Semantics is
  proposition-valued throughout. The Certification Dichotomy is indexed by
  decidability of diagonal acceptance, and `DICHOTOMY_SHARPNESS_CONTRACT`
  shows that this premise cannot be dropped. `ASCENT_HIERARCHY_CONTRACT`,
  `ASCENT_BOUNDS_CONTRACT`, and `PROLIFERATION_CONTRACT` take a bounded
  certification family, which `BRUTE_FORCE_EVALUATION_CONTRACT` supplies for
  the concrete language relative to every oracle;
  `CONCRETE_HIERARCHY_CONTRACT` is the resulting unconditional instance.
  `LOEB_CONTRACT`, `GOEDEL_SECOND_CONTRACT`, and the language-level Gödel
  clause are conditional on `HilbertKS` and `DerivabilityConditions`.

*)

From L003 Require Export L003_12__Relativized_SAT.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              DIAGONAL LANGUAGES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Lawvere's fixed-point theorem at the level of types.
│
*)

Definition LAWVERE_FIXED_POINT_CONTRACT : Prop :=
  forall (A Y : Type) (f : A -> A -> Y),
    PointSurjective f ->
    forall t : Y -> Y,
      exists y : Y, t y = y.

Definition BOOL_NO_POINT_SURJECTION_CONTRACT : Prop :=
  forall (A : Type) (f : A -> A -> bool),
    ~ PointSurjective f.

(*
│
│          Diagonal escape: `u` and `d_u` are not equivalent at the
│          quotation of `d_u`.
│
*)

Definition DIAGONAL_ESCAPE_CONTRACT : Prop :=
  forall (D : DiagonalStructure) (u : ds_expr D),
    ~ (ds_sem D u
         (ds_pair D (ds_code D (diagonal_of D u)) (ds_code D (diagonal_of D u)))
       <-> ds_sem D (diagonal_of D u) (ds_code D (diagonal_of D u))).

(*
│
│          Evaluator Ascent.
│
*)

Definition EVALUATOR_ASCENT_CONTRACT : Prop :=
  forall (D : DiagonalStructure) (u : ds_expr D) (n : nat),
    Evaluates D u n ->
    n < ds_level D u + ds_dup_cost D + ds_neg_cost D.

(*
│
│          No internal total classifier: globally, and locally for
│          diagonal-closed levels; under strictly increasing formation
│          levels every diagonal-closed level is empty.
│
*)

Definition NO_INTERNAL_CLASSIFIER_CONTRACT : Prop :=
  (forall D : DiagonalStructure,
     ~ exists u,
         forall e x,
           ds_sem D u (ds_pair D (ds_code D e) x) <-> ds_sem D e x) /\
  (forall (D : DiagonalStructure) (n : nat),
     DiagonalClosed D n ->
     forall u,
       ds_level D u <= n ->
       ~ Evaluates D u n) /\
  (forall (D : DiagonalStructure) (n : nat),
     (forall e, ds_level D e < ds_level D (ds_neg D e)) ->
     (forall e, ds_level D e < ds_level D (ds_dup D e)) ->
     DiagonalClosed D n ->
     forall e, n < ds_level D e).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                CERTIFICATION                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Certification Ascent.
│
*)

Definition CERTIFICATION_ASCENT_CONTRACT : Prop :=
  forall (C : CertificationStructure) (v : ds_expr C) (n : nat),
    SoundFor C v n ->
    CompleteFor C v n ->
    n < ds_level C v + cs_proj_cost C + ds_dup_cost C + ds_neg_cost C.

(*
│
│          Coding-free identity: at every datum, the diagonal sentence
│          holds exactly when no witness makes the verifier hold of
│          the duplicated datum. Abstract, size-free, and concrete
│          forms; no property of quotation is used.
│
*)

Definition CODING_FREE_IDENTITY_CONTRACT : Prop :=
  (forall (C : CertificationStructure) (v : ds_expr C) (x : ds_data C),
     ds_sem C (diagonal_sentence C v) x <->
     ~ exists w, ds_sem C v (ds_pair C (ds_pair C x x) (cs_wit C w))) /\
  (forall (R : SizeFreeLanguage) (v : sf_expr R) (x : sf_data R),
     sf_sem R (size_free_diagonal_sentence R v) x <->
     ~ exists w, sf_sem R v (sf_pair R (sf_pair R x x) (sf_wit R w))) /\
  (forall (O : Oracle) (v : ConcreteTerm) (x : BitStream),
     term_sem O (diagonal_term v) x <->
     ~ exists w, term_sem O v (stream_pair (stream_pair x x) w)).

(*
│
│          Self-application and the certification fixed point: the
│          diagonal claim is the negated projection claim, and it
│          holds exactly when the verifier does not accept it.
│
*)

Definition SELF_APPLICATION_CONTRACT : Prop :=
  forall (C : CertificationStructure) (v : ds_expr C),
    (DiagonalClaim C v <->
     ~ ds_sem C (cs_proj C v)
         (ds_pair C
           (ds_code C (diagonal_sentence C v))
           (ds_code C (diagonal_sentence C v)))) /\
    (DiagonalClaim C v <-> ~ DiagonalAccepted C v).

(*
│
│          Certification Dichotomy: for every verifier the dichotomy
│          is equivalent to decidability of its diagonal acceptance,
│          and its branches are exclusive; decidable semantics, in
│          particular Boolean semantics, yields it for every verifier.
│
*)

Definition CERTIFICATION_DICHOTOMY_CONTRACT : Prop :=
  (forall (C : CertificationStructure) (v : ds_expr C),
     ((DiagonalAccepted C v \/ ~ DiagonalAccepted C v) <->
      CertificationFailsAtDiagonal C v) /\
     ~ ((DiagonalAccepted C v /\ ~ DiagonalClaim C v) /\
        (~ DiagonalAccepted C v /\ DiagonalClaim C v))) /\
  (forall C : CertificationStructure,
     DecidableSemantics C ->
     forall v, CertificationFailsAtDiagonal C v) /\
  (forall D : DiagonalStructure,
     BooleanSemantics D ->
     DecidableSemantics D).

(*
│
│          Sharpness: the dichotomy for verifiers complete at their
│          own diagonal claim is equivalent to excluded middle;
│          propositionally, the boundary schema already implies
│          excluded middle.
│
*)

Definition DICHOTOMY_SHARPNESS_CONTRACT : Prop :=
  ((forall (C : CertificationStructure) (v : ds_expr C),
      (DiagonalClaim C v -> DiagonalAccepted C v) ->
      CertificationFailsAtDiagonal C v) <->
   (forall Q : Prop, Q \/ ~ Q)) /\
  ((forall G A : Prop, (G <-> ~ A) -> (G -> A) -> ((A /\ ~ G) \/ (~ A /\ G))) ->
   forall Q : Prop, Q \/ ~ Q).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       INVARIANCE AND SIZE INDEPENDENCE                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Faithful interpretations preserve the diagonal sentence,
│          its claim, and its non-acceptance; acceptance, and with it
│          the dichotomy branch, is preserved when it is decided on
│          both sides.
│
*)

Definition FAITHFUL_INVARIANCE_CONTRACT : Prop :=
  forall (C D : CertificationStructure)
         (I : FaithfulInterpretation C D)
         (v : ds_expr C),
    fi_expr I (diagonal_sentence C v) = diagonal_sentence D (fi_expr I v) /\
    (DiagonalClaim D (fi_expr I v) <-> DiagonalClaim C v) /\
    (~ DiagonalAccepted D (fi_expr I v) <-> ~ DiagonalAccepted C v) /\
    ((DiagonalAccepted C v \/ ~ DiagonalAccepted C v) ->
     (DiagonalAccepted D (fi_expr I v) \/ ~ DiagonalAccepted D (fi_expr I v)) ->
     (DiagonalAccepted D (fi_expr I v) <-> DiagonalAccepted C v) /\
     ((DiagonalAccepted D (fi_expr I v) /\ ~ DiagonalClaim D (fi_expr I v)) <->
      (DiagonalAccepted C v /\ ~ DiagonalClaim C v)) /\
     ((~ DiagonalAccepted D (fi_expr I v) /\ DiagonalClaim D (fi_expr I v)) <->
      (~ DiagonalAccepted C v /\ DiagonalClaim C v))).

(*
│
│          Size-free fixed point: the diagonal claim is equivalent to
│          its non-acceptance.
│
*)

Definition SIZE_FREE_FIXED_POINT_CONTRACT : Prop :=
  forall (R : SizeFreeLanguage) (v : sf_expr R),
    SizeFreeDiagonalClaim R v <-> ~ SizeFreeDiagonalAccepted R v.

(*
│
│          Pointwise incompleteness: soundness at the diagonal claim
│          leaves it true and uncertified, so no verifier is sound and
│          complete there.
│
*)

Definition POINTWISE_INCOMPLETENESS_CONTRACT : Prop :=
  forall (R : SizeFreeLanguage) (v : sf_expr R),
    ((SizeFreeDiagonalAccepted R v -> SizeFreeDiagonalClaim R v) ->
     SizeFreeDiagonalClaim R v /\ ~ SizeFreeDiagonalAccepted R v) /\
    ((SizeFreeDiagonalAccepted R v -> SizeFreeDiagonalClaim R v) ->
     (SizeFreeDiagonalClaim R v -> SizeFreeDiagonalAccepted R v) ->
     False).

(*
│
│          Constructive boundary, sharp form: the dichotomy
│          disjunction is equivalent to acceptance, and acceptance to
│          its own decision.
│
*)

Definition CONSTRUCTIVE_BOUNDARY_CONTRACT : Prop :=
  forall G A : Prop,
    (G <-> ~ A) ->
    (G -> A) ->
    (~ G /\ ~ ~ A) /\
    (((A /\ ~ G) \/ (~ A /\ G)) <-> A) /\
    (A <-> (A \/ ~ A)).

(*
│
│          No internal truth predicate.
│
*)

Definition INTERNAL_TRUTH_OBSTRUCTION_CONTRACT : Prop :=
  forall R : SizeFreeLanguage,
    ~ exists u,
        forall e x,
          sf_sem R u (sf_pair R (sf_code R e) x) <-> sf_sem R e x.

(*
│
│          Size-free interpretations preserve the diagonal sentence,
│          the diagonal claim, and non-acceptance; acceptance and the
│          branch where acceptance is decided on both sides.
│
*)

Definition SIZE_FREE_INVARIANCE_CONTRACT : Prop :=
  forall (R T : SizeFreeLanguage)
         (I : SizeFreeInterpretation R T)
         (v : sf_expr R),
    sfi_expr I (size_free_diagonal_sentence R v) =
      size_free_diagonal_sentence T (sfi_expr I v) /\
    (SizeFreeDiagonalClaim T (sfi_expr I v) <-> SizeFreeDiagonalClaim R v) /\
    (~ SizeFreeDiagonalAccepted T (sfi_expr I v) <->
     ~ SizeFreeDiagonalAccepted R v) /\
    ((SizeFreeDiagonalAccepted R v \/ ~ SizeFreeDiagonalAccepted R v) ->
     (SizeFreeDiagonalAccepted T (sfi_expr I v) \/
      ~ SizeFreeDiagonalAccepted T (sfi_expr I v)) ->
     (SizeFreeDiagonalAccepted T (sfi_expr I v) <-> SizeFreeDiagonalAccepted R v) /\
     ((SizeFreeDiagonalAccepted T (sfi_expr I v) /\
       ~ SizeFreeDiagonalClaim T (sfi_expr I v)) <->
      (SizeFreeDiagonalAccepted R v /\ ~ SizeFreeDiagonalClaim R v)) /\
     ((~ SizeFreeDiagonalAccepted T (sfi_expr I v) /\
       SizeFreeDiagonalClaim T (sfi_expr I v)) <->
      (~ SizeFreeDiagonalAccepted R v /\ SizeFreeDiagonalClaim R v))).

(*
│
│          One semantics, two layers: forgetting levels and grading
│          trivially preserve the diagonal sentence, claim, and
│          acceptance.
│
*)

Definition ONE_SEMANTICS_CONTRACT : Prop :=
  (forall (C : CertificationStructure) (v : ds_expr C),
     size_free_diagonal_sentence (forget_levels C) v = diagonal_sentence C v /\
     (SizeFreeDiagonalClaim (forget_levels C) v <-> DiagonalClaim C v) /\
     (SizeFreeDiagonalAccepted (forget_levels C) v <-> DiagonalAccepted C v)) /\
  (forall (R : SizeFreeLanguage) (v : sf_expr R),
     diagonal_sentence (trivial_grading R) v = size_free_diagonal_sentence R v /\
     (DiagonalClaim (trivial_grading R) v <-> SizeFreeDiagonalClaim R v) /\
     (DiagonalAccepted (trivial_grading R) v <-> SizeFreeDiagonalAccepted R v)).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               ASCENT HIERARCHY                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Unconditional: no verifier is impredicatively closed at any
│          level, and every correct bounded certifier is predicative.
│
*)

Definition IMPREDICATIVE_CLOSURE_CONTRACT : Prop :=
  (forall (C : CertificationStructure) (v : ds_expr C) (n : nat),
     ~ ImpredicativelyClosed C v n) /\
  (forall (C : CertificationStructure) (v : ds_expr C) (n : nat),
     SoundFor C v n ->
     CompleteFor C v n ->
     PredicativeAt C v n).

(*
│
│          Settled one level up: under exact costs `g_v` lies exactly
│          the formation costs above `v`; every evaluator whose domain
│          contains `g_v` settles the diagonal claim and lies above
│          `v` plus the projection cost.
│
*)

Definition SETTLED_ONE_LEVEL_UP_CONTRACT : Prop :=
  (forall (C : CertificationStructure) (v : ds_expr C),
     ExactCosts C ->
     ds_level C (diagonal_sentence C v) =
     ds_level C v + cs_proj_cost C + ds_dup_cost C + ds_neg_cost C) /\
  (forall (C : CertificationStructure) (v B : ds_expr C) (n : nat),
     ds_level C (diagonal_sentence C v) <= n ->
     Evaluates C B n ->
     (ds_sem C B
        (ds_pair C (ds_code C (diagonal_sentence C v))
                   (ds_code C (diagonal_sentence C v))) <->
      DiagonalClaim C v)) /\
  (forall (C : CertificationStructure) (v B : ds_expr C) (n : nat),
     ExactCosts C ->
     ds_level C (diagonal_sentence C v) <= n ->
     Evaluates C B n ->
     ds_level C v + cs_proj_cost C < ds_level C B).

(*
│
│          Given a bounded certification family: strict ascent,
│          incorrectness of each certifier at its own diagonal claim,
│          and correctness of the next certifier there.
│
*)

Definition ASCENT_HIERARCHY_CONTRACT : Prop :=
  forall (C : CertificationStructure) (V : nat -> ds_expr C) (n0 : nat),
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

(*
│
│          Given a bounded certification family: each step rises by at
│          least one level and at most by the current certifier's
│          level plus the three formation costs.
│
*)

Definition ASCENT_BOUNDS_CONTRACT : Prop :=
  forall (C : CertificationStructure) (V : nat -> ds_expr C) (n0 : nat),
    BoundedCertificationFamily C V ->
    forall k,
      ascent_levels C V n0 k < ascent_levels C V n0 (S k) /\
      ascent_levels C V n0 (S k) <=
        ds_level C (V (ascent_levels C V n0 k)) +
        cs_proj_cost C + ds_dup_cost C + ds_neg_cost C /\
      n0 + k <= ascent_levels C V n0 k.

(*
│
│          Given a bounded certification family: the diagonal failure
│          points are pairwise distinct.
│
*)

Definition PROLIFERATION_CONTRACT : Prop :=
  forall (C : CertificationStructure) (V : nat -> ds_expr C) (n0 : nat),
    BoundedCertificationFamily C V ->
    forall i j,
      diagonal_sentence C (V (ascent_levels C V n0 i)) =
      diagonal_sentence C (V (ascent_levels C V n0 j)) ->
      i = j.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            INTERNAL CERTIFICATION                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Löb's theorem under K/S and D1-D3.
│
*)

Definition LOEB_CONTRACT : Prop :=
  forall (P : ProvabilityCalculus) (A L : pc_sent P),
    HilbertKS P ->
    DerivabilityConditions P ->
    pc_prov P (pc_imp P L (pc_imp P (pc_box P L) A)) ->
    pc_prov P (pc_imp P (pc_imp P (pc_box P L) A) L) ->
    pc_prov P (pc_imp P (pc_box P A) A) ->
    pc_prov P A.

(*
│
│          Gödel II under K/S and D1-D3, given a certified fixed point
│          of `~ box`.
│
*)

Definition GOEDEL_SECOND_CONTRACT : Prop :=
  forall (P : ProvabilityCalculus) (G : pc_sent P),
    HilbertKS P ->
    DerivabilityConditions P ->
    pc_prov P (pc_imp P G (pc_neg P (pc_box P G))) ->
    pc_prov P (pc_imp P (pc_neg P (pc_box P G)) G) ->
    pc_prov P (pc_neg P (pc_box P (pc_bot P))) ->
    pc_prov P (pc_bot P).

(*
│
│          Language level: the certified fixed point needs only K/S,
│          box representation, and the certified negation and
│          duplication rules; the Gödel II clause additionally uses
│          D1-D3.
│
*)

Definition LANGUAGE_FIXED_POINT_CONTRACT : Prop :=
  (forall Lc : LanguageCalculus,
     HilbertKS Lc ->
     LanguageBoxRepresentation Lc ->
     CertifiedNegDupRules Lc ->
     pc_prov Lc
       (pc_imp Lc (language_diagonal_sentence Lc)
                  (pc_neg Lc (pc_box Lc (language_diagonal_sentence Lc)))) /\
     pc_prov Lc
       (pc_imp Lc (pc_neg Lc (pc_box Lc (language_diagonal_sentence Lc)))
                  (language_diagonal_sentence Lc))) /\
  (forall Lc : LanguageCalculus,
     HilbertKS Lc ->
     DerivabilityConditions Lc ->
     LanguageBoxRepresentation Lc ->
     CertifiedNegDupRules Lc ->
     ~ pc_prov Lc (pc_bot Lc) ->
     ~ pc_prov Lc (language_diagonal_sentence Lc) /\
     ~ pc_prov Lc (pc_neg Lc (pc_box Lc (pc_bot Lc)))).

(*
│
│          The internal premises are satisfiable: a consistent
│          calculus satisfies K/S and D1-D3, has a certified fixed
│          point of `~ box`, validates Löb's axiom, and does not prove
│          `~ box bot`; and a consistent language calculus satisfies
│          K/S, D1-D3, box representation, and the certified negation
│          and duplication rules, so it certifies neither its diagonal
│          sentence nor its consistency.
│
*)

Definition INTERNAL_MODEL_CONTRACT : Prop :=
  (exists P : ProvabilityCalculus,
     HilbertKS P /\
     DerivabilityConditions P /\
     ~ pc_prov P (pc_bot P) /\
     (exists G,
        pc_prov P (pc_imp P G (pc_neg P (pc_box P G))) /\
        pc_prov P (pc_imp P (pc_neg P (pc_box P G)) G)) /\
     (forall a,
        pc_prov P (pc_imp P (pc_box P (pc_imp P (pc_box P a) a)) (pc_box P a))) /\
     ~ pc_prov P (pc_neg P (pc_box P (pc_bot P)))) /\
  (exists Lc : LanguageCalculus,
     HilbertKS Lc /\
     DerivabilityConditions Lc /\
     LanguageBoxRepresentation Lc /\
     CertifiedNegDupRules Lc /\
     ~ pc_prov Lc (pc_bot Lc) /\
     ~ pc_prov Lc (language_diagonal_sentence Lc) /\
     ~ pc_prov Lc (pc_neg Lc (pc_box Lc (pc_bot Lc)))).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CONCRETE LANGUAGE                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Concrete grading: serialization parses uniquely; levels are
│          serialization lengths with exact formation costs three, so
│          `g_v` lies exactly nine bits above `v`, every
│          diagonal-closed level is empty, and node count is at most a
│          third of the level.
│
*)

Definition CONCRETE_GRADING_CONTRACT : Prop :=
  (forall t t' s s',
     term_serialize t ++ s = term_serialize t' ++ s' ->
     t = t' /\ s = s') /\
  (forall s,
     term_level (TNot s) = 3 + term_level s /\
     term_level (TDup s) = 3 + term_level s /\
     term_level (TProj s) = 3 + term_level s) /\
  (forall O : Oracle, ExactCosts (concrete_structure O)) /\
  (forall v, term_level (diagonal_term v) = term_level v + 9) /\
  (forall (O : Oracle) n,
     DiagonalClosed (concrete_structure O) n ->
     forall e, n < term_level e) /\
  (forall (O : Oracle) n,
     DiagonalClosed (concrete_structure O) n ->
     ~ exists e, term_level e <= n) /\
  (forall t, 3 * term_size t <= term_level t).

(*
│
│          Brute force inside the language, relative to every oracle:
│          `BF_n` evaluates level `n`, every evaluator of level `n`
│          lies above `n - 6`, `BF_n` itself has level at least
│          `3^(n+1) - 3`, and the certifiers read off from `BF_n` form
│          a bounded certification family.
│
*)

Definition BRUTE_FORCE_EVALUATION_CONTRACT : Prop :=
  forall O : Oracle,
    (forall n,
       Evaluates (concrete_structure O) (brute_force n) n /\
       (forall B,
          Evaluates (concrete_structure O) B n ->
          n < term_level B + 6)) /\
    (forall n, 3 ^ S n <= term_level (brute_force n) + 3) /\
    (forall n,
       term_level (brute_force n) <= term_level (concrete_certifier n) /\
       3 ^ S n <= term_level (concrete_certifier n) + 3) /\
    BoundedCertificationFamily (concrete_structure O) concrete_certifier.

(*
│
│          The unconditional concrete hierarchy relative to every
│          oracle: strict ascent by exactly the certifier's level plus
│          nine, incorrectness at each own diagonal claim, correction
│          by the next certifier, growth at least exponential per
│          step, and proliferation.
│
*)

Definition CONCRETE_HIERARCHY_CONTRACT : Prop :=
  (forall (O : Oracle) n0 k,
     ascent_levels (concrete_structure O) concrete_certifier n0 k <
       ascent_levels (concrete_structure O) concrete_certifier n0 (S k) /\
     ascent_levels (concrete_structure O) concrete_certifier n0 (S k) =
       term_level
         (concrete_certifier
           (ascent_levels (concrete_structure O) concrete_certifier n0 k)) + 9 /\
     ~ (DiagonalAccepted (concrete_structure O)
          (concrete_certifier
            (ascent_levels (concrete_structure O) concrete_certifier n0 k)) <->
        DiagonalClaim (concrete_structure O)
          (concrete_certifier
            (ascent_levels (concrete_structure O) concrete_certifier n0 k))) /\
     (Accepts (concrete_structure O)
        (concrete_certifier
          (ascent_levels (concrete_structure O) concrete_certifier n0 (S k)))
        (diagonal_term
          (concrete_certifier
            (ascent_levels (concrete_structure O) concrete_certifier n0 k)))
        (term_code
          (diagonal_term
            (concrete_certifier
              (ascent_levels (concrete_structure O) concrete_certifier n0 k))))
      <->
      DiagonalClaim (concrete_structure O)
        (concrete_certifier
          (ascent_levels (concrete_structure O) concrete_certifier n0 k)))) /\
  (forall (O : Oracle) n0 k,
     3 ^ S (ascent_levels (concrete_structure O) concrete_certifier n0 k) + 6 <=
     ascent_levels (concrete_structure O) concrete_certifier n0 (S k)) /\
  (forall (O : Oracle) n0 i j,
     diagonal_term
       (concrete_certifier
         (ascent_levels (concrete_structure O) concrete_certifier n0 i)) =
     diagonal_term
       (concrete_certifier
         (ascent_levels (concrete_structure O) concrete_certifier n0 j)) ->
     i = j).

(*
│
│          Relativization: the fixed point, brute-force evaluation,
│          the bounded family, and the diagonal sentence are uniform
│          in the oracle; oracle-free terms ignore it; and the oracle
│          genuinely changes truth.
│
*)

Definition RELATIVIZATION_CONTRACT : Prop :=
  (forall O : Oracle,
     (forall v, ConcreteDiagonalClaim O v <-> ~ ConcreteAccepted O v) /\
     (forall n, Evaluates (concrete_structure O) (brute_force n) n) /\
     BoundedCertificationFamily (concrete_structure O) concrete_certifier /\
     (forall v, diagonal_sentence (concrete_structure O) v = diagonal_term v)) /\
  (forall t, OracleFree t -> forall O O' x, term_sem O t x <-> term_sem O' t x) /\
  (term_sem (fun _ => True) (TOracle []) (fun _ => false) /\
   ~ term_sem empty_oracle (TOracle []) (fun _ => false)).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           PLAIN PROPOSITIONAL SAT                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Truth tables classify every propositional formula
│          correctly.
│
*)

Definition TRUTH_TABLE_CONTRACT : Prop :=
  forall f : PropFormula,
    classify f = true <-> Satisfiable f.

(*
│
│          Specialization of a circuit verifier at its diagonal claim,
│          relative to every oracle.
│
*)

Definition SPECIALIZATION_CONTRACT : Prop :=
  forall (O : Oracle) (v : ConcreteTerm),
    CircuitVerifier v ->
    (ConcreteAccepted O v <-> Satisfiable (specialized_formula v)) /\
    formula_size (specialized_formula v) <= term_size v /\
    3 * formula_size (specialized_formula v) <= term_level v.

(*
│
│          The Solver's Paradox for plain SAT, relative to every
│          oracle, with the brute-force item.
│
*)

Definition SOLVERS_PARADOX_PLAIN_SAT_CONTRACT : Prop :=
  forall (O : Oracle) (v : ConcreteTerm),
    CircuitVerifier v ->
    formula_size (specialized_formula v) <= term_size v /\
    3 * formula_size (specialized_formula v) <= term_level v /\
    (classify (specialized_formula v) = true <->
     Satisfiable (specialized_formula v)) /\
    (term_level (diagonal_term v) = term_level v + 9 /\
     (term_sem O (brute_force (term_level (diagonal_term v)))
        (stream_pair (term_code (diagonal_term v)) (term_code (diagonal_term v)))
      <-> ConcreteDiagonalClaim O v) /\
     (forall B n,
        term_level (diagonal_term v) <= n ->
        Evaluates (concrete_structure O) B n ->
        term_level v + 3 < term_level B)) /\
    (ConcreteDiagonalClaim O v <-> ~ Satisfiable (specialized_formula v)) /\
    ((Satisfiable (specialized_formula v) /\ ConcreteAccepted O v /\
      ~ ConcreteDiagonalClaim O v) \/
     (~ Satisfiable (specialized_formula v) /\ ~ ConcreteAccepted O v /\
      ConcreteDiagonalClaim O v)) /\
    ~ ((Satisfiable (specialized_formula v) /\ ConcreteAccepted O v /\
        ~ ConcreteDiagonalClaim O v) /\
       (~ Satisfiable (specialized_formula v) /\ ~ ConcreteAccepted O v /\
        ConcreteDiagonalClaim O v)).

(*
│
│          The two minimal branches are realized by the constant
│          verifiers, relative to every oracle.
│
*)

Definition MINIMAL_BRANCHES_CONTRACT : Prop :=
  forall O : Oracle,
    (Satisfiable (specialized_formula (TConst true)) /\
     ConcreteAccepted O (TConst true) /\
     ~ ConcreteDiagonalClaim O (TConst true)) /\
    (~ Satisfiable (specialized_formula (TConst false)) /\
     ~ ConcreteAccepted O (TConst false) /\
     ConcreteDiagonalClaim O (TConst false)).

(*
│
│          Tseitin: equisatisfiable CNF with at most `3 |f| + 1`
│          clauses of width at most three and at most `|f|` fresh
│          variables; at the diagonal claim of a circuit verifier it
│          is linear in the verifier.
│
*)

Definition TSEITIN_CONTRACT : Prop :=
  (forall f : PropFormula,
     (Satisfiable f <-> CNFSatisfiable (tseitin f)) /\
     length (tseitin f) <= 3 * formula_size f + 1 /\
     (forall c, In c (tseitin f) -> length c <= 3) /\
     CNFBelow (tseitin f) (formula_var_bound f + formula_size f)) /\
  (forall (O : Oracle) (v : ConcreteTerm),
     CircuitVerifier v ->
     (ConcreteAccepted O v <-> CNFSatisfiable (tseitin (specialized_formula v))) /\
     length (tseitin (specialized_formula v)) <= 3 * term_size v + 1 /\
     length (tseitin (specialized_formula v)) <= term_level v + 1).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CODING SENSITIVITY                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Robust obstruction, coding-relative branch: under every
│          quotation the diagonal claim is equivalent to its
│          non-acceptance; both the standard and the negated quotation
│          are injective; `TBit 0` lands in opposite branches under
│          them; and no faithful interpretation that is the identity
│          on terms relates the two codings.
│
*)

Definition CODING_SENSITIVITY_CONTRACT : Prop :=
  (forall (O : Oracle) (q : Quotation) (v : ConcreteTerm),
     QuotedClaim O q v <-> ~ QuotedAccepted O q v) /\
  (forall e e', (forall i, term_code e i = term_code e' i) -> e = e') /\
  (forall e e', (forall i, neg_code e i = neg_code e' i) -> e = e') /\
  (forall O : Oracle,
     (~ QuotedAccepted O term_code (TBit 0) /\ QuotedClaim O term_code (TBit 0)) /\
     (QuotedAccepted O neg_code (TBit 0) /\ ~ QuotedClaim O neg_code (TBit 0))) /\
  (forall (O : Oracle)
          (I : FaithfulInterpretation (quoted_structure O term_code)
                                      (quoted_structure O neg_code)),
     ~ (forall e, fi_expr I e = e)).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            EVALUATOR LOWER BOUND                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Every internal evaluator of level `n` has level at least
│          `(n - 4) (n + 2)`: terms depend only on the positions they
│          read, each read of position `j` costs `j + 1` bits under
│          the unary index encoding, and an evaluator must read every
│          even position `2 (i + 3)` with `i + 5 <= n`. `BF_n` lies
│          between this bound and `3^(n+1) - 3`.
│
*)

Definition EVALUATOR_LOWER_BOUND_CONTRACT : Prop :=
  (forall (O : Oracle) t x y,
     (forall j, In j (reads t) -> x j = y j) ->
     term_sem O t x <-> term_sem O t y) /\
  (forall t, position_cost (reads t) <= term_level t) /\
  (forall (O : Oracle) u n i,
     Evaluates (concrete_structure O) u n ->
     i + 5 <= n ->
     In (2 * (i + 3)) (reads u)) /\
  (forall (O : Oracle) u n,
     Evaluates (concrete_structure O) u n ->
     (n - 4) * (n + 2) <= term_level u) /\
  (forall n,
     (n - 4) * (n + 2) <= term_level (brute_force n) /\
     3 ^ S n <= term_level (brute_force n) + 3).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               RELATIVIZED SAT                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The SAT specialization relative to every Boolean oracle:
│          relativized truth tables are correct; every oracle circuit
│          specializes to an oracle formula no larger than itself
│          whose relative satisfiability is its acceptance; the
│          paradox holds with both branches decided; circuit verifiers
│          are oracle circuits; and on oracle-free formulas and
│          circuit verifiers the relativized classifier agrees with
│          the plain one.
│
*)

Definition RELATIVIZED_SAT_CONTRACT : Prop :=
  (forall (ob : BoolOracle) (f : OFormula),
     oclassify ob f = true <-> OSatisfiable ob f) /\
  (forall t, CircuitVerifier t -> OracleCircuit t) /\
  (forall (ob : BoolOracle) (f : PropFormula),
     oclassify ob (embed_formula f) = classify f) /\
  (forall (ob : BoolOracle) (v : ConcreteTerm),
     CircuitVerifier v ->
     oracle_specialized_formula v = embed_formula (specialized_formula v) /\
     oclassify ob (oracle_specialized_formula v) = classify (specialized_formula v)) /\
  (forall (ob : BoolOracle) (v : ConcreteTerm),
     OracleCircuit v ->
     (ConcreteAccepted (bool_oracle ob) v <->
      OSatisfiable ob (oracle_specialized_formula v)) /\
     oformula_size (oracle_specialized_formula v) <= term_size v /\
     3 * oformula_size (oracle_specialized_formula v) <= term_level v) /\
  (forall (ob : BoolOracle) (v : ConcreteTerm),
     OracleCircuit v ->
     (ConcreteDiagonalClaim (bool_oracle ob) v <->
      ~ OSatisfiable ob (oracle_specialized_formula v)) /\
     CertificationFailsAtDiagonal (concrete_structure (bool_oracle ob)) v).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                  AGGREGATES                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Primary theorem core.
│
*)

Definition L003_CORE_CONTRACT : Prop :=
  CODING_FREE_IDENTITY_CONTRACT /\
  CERTIFICATION_DICHOTOMY_CONTRACT /\
  SIZE_FREE_FIXED_POINT_CONTRACT /\
  BRUTE_FORCE_EVALUATION_CONTRACT /\
  SOLVERS_PARADOX_PLAIN_SAT_CONTRACT.

(*
│
│          Every L003 contract in proof order.
│
*)

Definition L003_CONTRACT : Prop :=
  LAWVERE_FIXED_POINT_CONTRACT /\
  BOOL_NO_POINT_SURJECTION_CONTRACT /\
  DIAGONAL_ESCAPE_CONTRACT /\
  EVALUATOR_ASCENT_CONTRACT /\
  NO_INTERNAL_CLASSIFIER_CONTRACT /\
  CERTIFICATION_ASCENT_CONTRACT /\
  CODING_FREE_IDENTITY_CONTRACT /\
  SELF_APPLICATION_CONTRACT /\
  CERTIFICATION_DICHOTOMY_CONTRACT /\
  DICHOTOMY_SHARPNESS_CONTRACT /\
  FAITHFUL_INVARIANCE_CONTRACT /\
  SIZE_FREE_FIXED_POINT_CONTRACT /\
  POINTWISE_INCOMPLETENESS_CONTRACT /\
  CONSTRUCTIVE_BOUNDARY_CONTRACT /\
  INTERNAL_TRUTH_OBSTRUCTION_CONTRACT /\
  SIZE_FREE_INVARIANCE_CONTRACT /\
  ONE_SEMANTICS_CONTRACT /\
  IMPREDICATIVE_CLOSURE_CONTRACT /\
  SETTLED_ONE_LEVEL_UP_CONTRACT /\
  ASCENT_HIERARCHY_CONTRACT /\
  ASCENT_BOUNDS_CONTRACT /\
  PROLIFERATION_CONTRACT /\
  LOEB_CONTRACT /\
  GOEDEL_SECOND_CONTRACT /\
  LANGUAGE_FIXED_POINT_CONTRACT /\
  INTERNAL_MODEL_CONTRACT /\
  CONCRETE_GRADING_CONTRACT /\
  BRUTE_FORCE_EVALUATION_CONTRACT /\
  CONCRETE_HIERARCHY_CONTRACT /\
  RELATIVIZATION_CONTRACT /\
  TRUTH_TABLE_CONTRACT /\
  SPECIALIZATION_CONTRACT /\
  SOLVERS_PARADOX_PLAIN_SAT_CONTRACT /\
  MINIMAL_BRANCHES_CONTRACT /\
  TSEITIN_CONTRACT /\
  CODING_SENSITIVITY_CONTRACT /\
  EVALUATOR_LOWER_BOUND_CONTRACT /\
  RELATIVIZED_SAT_CONTRACT.
