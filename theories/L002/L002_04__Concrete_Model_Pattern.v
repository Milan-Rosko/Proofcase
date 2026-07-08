(*L002_04__Concrete_Model_Pattern.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / L002_04__Concrete_Model_Pattern                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Concrete model pattern for L002. The earlier layers state the
  recursive-pressure vocabulary parametrically over an arbitrary model
  family. This file instantiates that interface with the smallest useful
  model: one concrete model state, one distinguished authority formula, a
  matching local derivability and `AsIF` surface, a counter-approximation
  predicate against the authority formula, depth-indexed pressure `S depth`,
  and stability as bounded pressure. The result is not intended as an
  empirical model; it is a certified reusable pattern showing that the
  abstract bridge laws have a non-vacuous concrete instance.

*)

From L002 Require Export L002_03__Symbolic_Regulator_Principles.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             CONCRETE MODEL DATA                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Inductive ConcreteModel : Type :=
| concrete_model : ConcreteModel.

Definition concrete_authority_formula : Formula :=
  Imp Bot Bot.

Definition concrete_counter_formula : Formula :=
  formula_negation concrete_authority_formula.

Definition concrete_derives : ModelDerivability ConcreteModel :=
  fun _ A => A = concrete_authority_formula.

Definition concrete_asif : AsIFFor ConcreteModel :=
  fun _ A => A = concrete_authority_formula.

Definition concrete_approximates : RecursiveApproximation ConcreteModel :=
  fun _ A => A = concrete_counter_formula.

Definition concrete_recursive_depth
    (m : ConcreteModel)
    (A : Formula)
    (depth : nat) : Prop :=
  concrete_approximates m A.

Definition concrete_penalty (_ : ConcreteModel) : nat :=
  1.

Definition concrete_penalty_at_depth
    (depth : nat)
    (_ : ConcreteModel) : nat :=
  S depth.

Definition concrete_stable (m : ConcreteModel) : Prop :=
  exists bound : nat,
    forall depth : nat,
      concrete_penalty_at_depth depth m <= bound.

Definition concrete_fragmented (_ : ConcreteModel) : Prop :=
  False.

Definition concrete_recursive_structure :
    RecursiveApproximationStructure ConcreteModel :=
  {|
    approximates := concrete_approximates;
    RecursiveDepth := concrete_recursive_depth;
    Penalty := concrete_penalty;
    PenaltyAtDepth := concrete_penalty_at_depth;
    Stable := concrete_stable;
    Fragmented := concrete_fragmented
  |}.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             CONCRETE BRIDGE LAWS                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Theorem concrete_model_local_authority :
  ModelLocalAuthority
    ConcreteModel
    concrete_derives
    concrete_asif.
Proof.
  intros m A Hasif.
  exact Hasif.
Qed.

Theorem concrete_recursive_approximation_cost :
  RecursiveApproximationCost
    ConcreteModel
    concrete_recursive_structure.
Proof.
  intros m A _Happrox.
  unfold concrete_recursive_structure.
  simpl.
  apply le_n.
Qed.

Theorem concrete_penalty_accumulates :
  PenaltyAccumulates
    ConcreteModel
    concrete_recursive_structure.
Proof.
  intros depth m.
  unfold concrete_recursive_structure.
  simpl.
  apply le_S.
  apply le_n.
Qed.

Theorem concrete_recursive_approximation_depth_cost :
  RecursiveApproximationDepthCost
    ConcreteModel
    concrete_recursive_structure.
Proof.
  intros depth m A _Happrox.
  unfold concrete_recursive_structure.
  simpl.
  apply le_n.
Qed.

Theorem concrete_recursive_depth_positive_penalty :
  RecursiveDepthPositivePenalty
    ConcreteModel
    concrete_recursive_structure.
Proof.
  intros m A depth _Hdepth.
  unfold concrete_recursive_structure.
  simpl.
  apply le_n_S.
  apply le_0_n.
Qed.

Theorem concrete_recursive_authority_pressure :
  RecursiveAuthorityPressure
    ConcreteModel
    concrete_asif
    concrete_recursive_structure.
Proof.
  intros m A _Hasif _Happrox.
  unfold concrete_recursive_structure.
  simpl.
  apply le_n.
Qed.

Theorem concrete_recursive_authority_depth_pressure :
  RecursiveAuthorityDepthPressure
    ConcreteModel
    concrete_asif
    concrete_recursive_structure.
Proof.
  intros depth m A _Hasif _Happrox.
  unfold concrete_recursive_structure.
  simpl.
  apply le_n.
Qed.

Theorem concrete_stable_requires_bounded_recursive_pressure :
  StableRequiresBoundedRecursivePressure
    ConcreteModel
    concrete_recursive_structure.
Proof.
  intros m Hstable.
  unfold concrete_recursive_structure in Hstable.
  simpl in Hstable.
  destruct Hstable as [bound Hbound].
  exists bound.
  exact Hbound.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         CONCRETE PRESSURE ENDPOINTS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Theorem concrete_counter_certification_at_authority :
  forall (depth : nat) (m : ConcreteModel),
    CounterCertificationAt
      ConcreteModel
      concrete_recursive_structure
      depth
      m
      concrete_authority_formula.
Proof.
  intros depth m.
  unfold CounterCertificationAt.
  unfold concrete_recursive_structure.
  simpl.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Theorem concrete_nested_authority_pressure_at_authority :
  forall (depth : nat) (m : ConcreteModel),
    NestedAuthorityPressure
      ConcreteModel
      concrete_asif
      concrete_recursive_structure
      depth
      m
      concrete_authority_formula.
Proof.
  intros depth m.
  unfold NestedAuthorityPressure.
  unfold concrete_recursive_structure.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * apply le_n_S.
        apply le_0_n.
Qed.

Theorem concrete_authority_counter_certification_yields_recursive_pressure :
  forall (depth : nat) (m : ConcreteModel),
    concrete_derives m concrete_authority_formula /\
    NestedAuthorityPressure
      ConcreteModel
      concrete_asif
      concrete_recursive_structure
      depth
      m
      concrete_authority_formula.
Proof.
  intros depth m.
  exact
    (local_authority_counter_certification_yields_recursive_pressure
       ConcreteModel
       concrete_derives
       concrete_asif
       concrete_recursive_structure
       depth
       m
       concrete_authority_formula
       concrete_model_local_authority
       concrete_recursive_depth_positive_penalty
       eq_refl
       (concrete_counter_certification_at_authority depth m)).
Qed.

Theorem concrete_authority_penalty_increases :
  forall (depth : nat) (m : ConcreteModel),
    PenaltyAtDepth concrete_recursive_structure depth m <
    PenaltyAtDepth concrete_recursive_structure (S depth) m.
Proof.
  intros depth m.
  exact
    (nested_authority_pressure_increases_penalty_at_depth
       ConcreteModel
       concrete_asif
       concrete_recursive_structure
       depth
       m
       concrete_authority_formula
       concrete_recursive_authority_depth_pressure
       (concrete_nested_authority_pressure_at_authority depth m)).
Qed.

Theorem concrete_unbounded_recursive_pressure :
  forall m : ConcreteModel,
    UnboundedRecursivePressure
      ConcreteModel
      concrete_recursive_structure
      m.
Proof.
  intro m.
  exact
    (strict_depth_pressure_unbounded
       ConcreteModel
       concrete_recursive_structure
       m
       (fun depth => concrete_authority_penalty_increases depth m)).
Qed.

Theorem concrete_nested_authority_pressure_obstructs_stability :
  forall m : ConcreteModel,
    ~ Stable concrete_recursive_structure m.
Proof.
  intro m.
  exact
    (nested_authority_pressure_obstructs_stability
       ConcreteModel
       concrete_asif
       concrete_recursive_structure
       m
       concrete_authority_formula
       concrete_recursive_authority_depth_pressure
       (fun depth => concrete_nested_authority_pressure_at_authority depth m)
       concrete_stable_requires_bounded_recursive_pressure).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           CONCRETE PATTERN WITNESS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition CONCRETE_MODEL_PATTERN : Prop :=
  ModelLocalAuthority
    ConcreteModel
    concrete_derives
    concrete_asif /\
  RecursiveApproximationCost
    ConcreteModel
    concrete_recursive_structure /\
  PenaltyAccumulates
    ConcreteModel
    concrete_recursive_structure /\
  RecursiveApproximationDepthCost
    ConcreteModel
    concrete_recursive_structure /\
  RecursiveDepthPositivePenalty
    ConcreteModel
    concrete_recursive_structure /\
  RecursiveAuthorityPressure
    ConcreteModel
    concrete_asif
    concrete_recursive_structure /\
  RecursiveAuthorityDepthPressure
    ConcreteModel
    concrete_asif
    concrete_recursive_structure /\
  StableRequiresBoundedRecursivePressure
    ConcreteModel
    concrete_recursive_structure /\
  (forall (depth : nat) (m : ConcreteModel),
     CounterCertificationAt
       ConcreteModel
       concrete_recursive_structure
       depth
       m
       concrete_authority_formula) /\
  (forall (depth : nat) (m : ConcreteModel),
     NestedAuthorityPressure
       ConcreteModel
       concrete_asif
       concrete_recursive_structure
       depth
       m
       concrete_authority_formula) /\
  (forall (depth : nat) (m : ConcreteModel),
     concrete_derives m concrete_authority_formula /\
     NestedAuthorityPressure
       ConcreteModel
       concrete_asif
       concrete_recursive_structure
       depth
       m
       concrete_authority_formula) /\
  (forall (depth : nat) (m : ConcreteModel),
     PenaltyAtDepth concrete_recursive_structure depth m <
     PenaltyAtDepth concrete_recursive_structure (S depth) m) /\
  (forall m : ConcreteModel,
     UnboundedRecursivePressure
       ConcreteModel
       concrete_recursive_structure
       m) /\
  (forall m : ConcreteModel,
     ~ Stable concrete_recursive_structure m).

Theorem concrete_model_pattern :
  CONCRETE_MODEL_PATTERN.
Proof.
  unfold CONCRETE_MODEL_PATTERN.
  exact
    (conj
       concrete_model_local_authority
       (conj
          concrete_recursive_approximation_cost
          (conj
             concrete_penalty_accumulates
             (conj
                concrete_recursive_approximation_depth_cost
                (conj
                   concrete_recursive_depth_positive_penalty
                   (conj
                      concrete_recursive_authority_pressure
                      (conj
                         concrete_recursive_authority_depth_pressure
                         (conj
                            concrete_stable_requires_bounded_recursive_pressure
                            (conj
                               concrete_counter_certification_at_authority
                               (conj
                                  concrete_nested_authority_pressure_at_authority
                                  (conj
                                     concrete_authority_counter_certification_yields_recursive_pressure
                                     (conj
                                        concrete_authority_penalty_increases
                                        (conj
                                           concrete_unbounded_recursive_pressure
                                           concrete_nested_authority_pressure_obstructs_stability))))))))))))).
Qed.
