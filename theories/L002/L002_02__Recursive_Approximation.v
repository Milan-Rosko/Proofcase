(*L002_02__Recursive_Approximation.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / L002_02__Recursive_Approximation                 │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We abstract from the single embedded subsystem of the previous layer to an
  arbitrary family of embedded models. Local derivability, the `AsIF`
  admissibility surface, and an explicit recursive-approximation structure
  are carried as parameters to the theorems below. The structure exposes six
  primitives — `approximates`, `RecursiveDepth`, `Penalty`, `PenaltyAtDepth`,
  `Stable`, and `Fragmented` — each a parameter of the caller-supplied
  dynamics. No semantic truth predicate is introduced and no concrete model
  carrier is committed to.

  Two structural observations organize the layer. First, an embedded model
  whose local derivability is included in a surrounding regulator cannot
  stably combine an escape claim with a checked refutation of the authority
  surface that the escape reactivates. Second, recursive approximation of a
  regulator condition incurs graded stabilization pressure, so phenomena such
  as bounded introspection, threshold pressure, fragmentation, unbounded
  regress, and collapse can be stated separately rather than identified with
  immediate inconsistency.

  The graded picture is the layer's main contribution. The same mismatch
  between an embedded model and the regulator that records it can apply at
  successive nested levels — a model of perception inside a model that
  includes that perception, and so on. The recursive-approximation structure
  does not commit to a particular nesting; it only insists that each step
  accumulates pressure, and that stable continuation requires a finite bound
  on that pressure across recursive depth.

*)

From L002 Require Export L002_01__Mirror_Unrefutability.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          ABSTRACT MODEL VOCABULARY                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `ModelDerivability Model` is the local-derivability surface
│          for an abstract family of embedded models. It is a
│          caller-supplied Prop-valued predicate, not a new checker;
│          the layer transports it through operational theorems but
│          does not interpret it.
│
*)

Definition ModelDerivability (Model : Type) : Type :=
  Model -> Formula -> Prop.

(*
│
│          `AsIFFor Model` is the model-indexed admissibility surface:
│          `asif m A` says that formula `A` is regulator-admissible
│          for the embedded model `m`. It generalizes the
│          single-subsystem `AsIF` of `L002_00` to an indexed family.
│
*)

Definition AsIFFor (Model : Type) : Type :=
  Model -> Formula -> Prop.

(*
│
│          `ModelAdmissibility Model` is a compatibility spelling for
│          `AsIFFor Model`. New statements use `AsIFFor` when the
│          model argument is explicit.
│
*)

Definition ModelAdmissibility (Model : Type) : Type :=
  AsIFFor Model.

(*
│
│          `StablePredicate Model` is the type of stable-continuation
│          predicates over embedded models. The layer does not define
│          a stability metric of its own; it only transports an
│          explicit stability hypothesis through the operational
│          theorems.
│
*)

Definition StablePredicate (Model : Type) : Type :=
  Model -> Prop.

(*
│
│          `ModelStability` is a compatibility spelling for
│          `StablePredicate`. Working with recursive dynamics, prefer
│          the `Stable` field of `RecursiveApproximationStructure`
│          introduced below.
│
*)

Definition ModelStability (Model : Type) : Type :=
  StablePredicate Model.

(*
│
│          `RecursiveApproximation Model` records that an embedded
│          model approximates a regulator condition expressed by a
│          formula. The predicate is structural: it carries no
│          semantic accuracy claim and does not commit the model to
│          actually realizing the condition.
│
*)

Definition RecursiveApproximation (Model : Type) : Type :=
  Model -> Formula -> Prop.

(*
│
│          `ModelApproximation` is a compatibility spelling for
│          `RecursiveApproximation`. New statements use the latter.
│
*)

Definition ModelApproximation (Model : Type) : Type :=
  RecursiveApproximation Model.

(*
│
│          `PenaltyMeasure Model` is the type of natural-number
│          pressure measures attached to embedded models. The layer is
│          parametric in the measure; later work may instantiate it
│          with a concrete stabilization metric.
│
*)

Definition PenaltyMeasure (Model : Type) : Type :=
  Model -> nat.

(*
│
│          `ModelPenalty` is a compatibility spelling for
│          `PenaltyMeasure`. Working with recursive dynamics, prefer
│          the `Penalty` field of `RecursiveApproximationStructure`.
│
*)

Definition ModelPenalty (Model : Type) : Type :=
  PenaltyMeasure Model.

(*
│
│          `InfiniteRecursiveApproximation Model` names the
│          caller-supplied condition that a model engages in unbounded
│          recursive approximation. The layer treats it abstractly:
│          the destabilization principle below converts the condition
│          into loss of stable continuation.
│
*)

Definition InfiniteRecursiveApproximation (Model : Type) : Type :=
  Model -> Prop.

(*
│
│          `RecursiveApproximationStructure Model` packages the
│          recursive-dynamics primitives for an embedded model family.
│          The record bundles an approximation relation, a
│          depth-indexed recursive-depth predicate, an aggregate
│          penalty measure, a depth-indexed penalty measure, a
│          stable-continuation predicate, and a fragmentation
│          predicate. Each field is a parameter of the caller-supplied
│          dynamics; the layer fixes the interface and proves theorems
│          quantified over any such structure.
│
*)

Record RecursiveApproximationStructure (Model : Type) : Type := {
  approximates : Model -> Formula -> Prop;
  RecursiveDepth : Model -> Formula -> nat -> Prop;
  Penalty : Model -> nat;
  PenaltyAtDepth : nat -> Model -> nat;
  Stable : Model -> Prop;
  Fragmented : Model -> Prop
}.

Arguments approximates {Model} _ _ _.
Arguments RecursiveDepth {Model} _ _ _ _.
Arguments Penalty {Model} _ _.
Arguments PenaltyAtDepth {Model} _ _ _.
Arguments Stable {Model} _ _.
Arguments Fragmented {Model} _ _.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            STRUCTURAL INTERFACES                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `ModelEmbeddedInRegulator` is the inclusion interface for
│          an embedded model. It states that every formula locally
│          derived by the model is checked-derivable by `Sλ` at the
│          working context. This generalizes
│          `regulator_theory_included` from `L002_00` to a
│          derivability relation that is not itself an M001 checker.
│
*)

(*                      ∀m, A. derives(m, A) ⇒ Sλ ⊢_Γ A.                      *)

Definition ModelEmbeddedInRegulator
    (Model : Type)
    (Slambda : RegulatorTheory)
    (Gamma : Context)
    (derives : ModelDerivability Model) : Prop :=
  forall (m : Model) (A : Formula),
    derives m A ->
    regulator_theory_checked_derivable Slambda Gamma A.

(*
│
│          `ModelModusPonens` is the local closure principle for an
│          abstract derivability relation. It is stated explicitly
│          because model derivability is not assumed to be an M001
│          checker and therefore does not automatically inherit modus
│          ponens.
│
*)

(*        ∀m, A, B. derives(m, A ⇒ B) ∧ derives(m, A) ⇒ derives(m, B).        *)

Definition ModelModusPonens
    (Model : Type)
    (derives : ModelDerivability Model) : Prop :=
  forall (m : Model) (A B : Formula),
    derives m (Imp A B) ->
    derives m A ->
    derives m B.

(*
│
│          `ModelLocalAuthority` is the model-indexed counterpart of
│          `LocalAuthority`: regulator-admissibility for the model is
│          internalized as actual local derivability for that model.
│
*)

(*                     ∀m, A. asif(m, A) ⇒ derives(m, A).                     *)

Definition ModelLocalAuthority
    (Model : Type)
    (derives : ModelDerivability Model)
    (asif : AsIFFor Model) : Prop :=
  forall (m : Model) (A : Formula),
    asif m A ->
    derives m A.

(*
│
│          `ModelEscapeReabsorbed` is the model-indexed reabsorption
│          mechanism: if `m` locally derives an escape claim, the act
│          re-enters the admissibility surface under the authority
│          formula `A`. The mechanism applies at each level of an
│          embedded family.
│
*)

(*                        derives(m, e) ⇒ asif(m, A).                         *)

Definition ModelEscapeReabsorbed
    (Model : Type)
    (derives : ModelDerivability Model)
    (asif : AsIFFor Model)
    (m : Model)
    (A escape_claim : Formula) : Prop :=
  derives m escape_claim ->
  asif m A.

(*
│
│          `RecursiveApproximationCost` is the basic cost interface:
│          every approximation act incurs positive stabilization
│          pressure under the caller-supplied penalty measure. The
│          interface does not specify how the pressure scales; it only
│          forbids approximation at zero cost.
│
*)

(*                ∀m, A. approximates(m, A) ⇒ 0 < Penalty(m).                 *)

Definition RecursiveApproximationCost
    (Model : Type)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall (m : Model) (A : Formula),
    approximates R m A ->
    0 < Penalty R m.

(*
│
│          `PenaltyAccumulates` is the weak monotonicity law over
│          recursive depth: advancing one step outward never decreases
│          the depth-indexed pressure. It is the formal expression of
│          the observation that wrapping an embedded model inside a
│          further embedding does not relieve the inner pressure.
│
*)

(*           ∀d, m. PenaltyAtDepth(d, m) ≤ PenaltyAtDepth(d+1, m).            *)

Definition PenaltyAccumulates
    (Model : Type)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall (depth : nat) (m : Model),
    PenaltyAtDepth R depth m <= PenaltyAtDepth R (S depth) m.

(*
│
│          `RecursiveApproximationDepthCost` strengthens the previous
│          law: when a model is in fact approximating, advancing one
│          depth step strictly increases the depth-indexed penalty.
│          This is the graded counterpart of identifying each nested
│          layer as an extra source of pressure.
│
*)

(* ∀d, m, A. approximates(m, A) ⇒ PenaltyAtDepth(d, m) < PenaltyAtDepth(d+1,  *)
(*                                    m).                                     *)

Definition RecursiveApproximationDepthCost
    (Model : Type)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall (depth : nat) (m : Model) (A : Formula),
    approximates R m A ->
    PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m.

(*
│
│          `RecursiveDepthPositivePenalty` is the depth-positivity
│          law: being at recursive depth `depth` for a formula carries
│          positive depth-indexed pressure. The law is graded by
│          design, so the package can speak of accumulation without
│          identifying every approximation act with immediate
│          inconsistency.
│
*)

(*       ∀m, A, d. RecursiveDepth(m, A, d) ⇒ 0 < PenaltyAtDepth(d, m).        *)

Definition RecursiveDepthPositivePenalty
    (Model : Type)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall (m : Model) (A : Formula) (depth : nat),
    RecursiveDepth R m A depth ->
    0 < PenaltyAtDepth R depth m.

(*
│
│          `RecursiveAuthorityPressure` is the bridge from authority
│          to recursive dynamics. If a model treats `A` as locally
│          authoritative while approximating its negation, the
│          approximation incurs positive stabilization pressure. The
│          configuration is exactly the embedded mismatch between a
│          self-model's authority surface and the regulator it cannot
│          internally certify against.
│
*)

(*         ∀m, A. asif(m, A) ∧ approximates(m, ¬A) ⇒ 0 < Penalty(m).          *)

Definition RecursiveAuthorityPressure
    (Model : Type)
    (asif : AsIFFor Model)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall (m : Model) (A : Formula),
    asif m A ->
    approximates R m (formula_negation A) ->
    0 < Penalty R m.

(*
│
│          `RecursiveAuthorityDepthPressure` is the depth-graded
│          version of the same bridge: approximating against a locally
│          authoritative surface strictly increases the depth-indexed
│          penalty at every step.
│
*)

(*    ∀d, m, A. asif(m, A) ∧ approximates(m, ¬A) ⇒ PenaltyAtDepth(d, m) <     *)
(*                          PenaltyAtDepth(d+1, m).                           *)

Definition RecursiveAuthorityDepthPressure
    (Model : Type)
    (asif : AsIFFor Model)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall (depth : nat) (m : Model) (A : Formula),
    asif m A ->
    approximates R m (formula_negation A) ->
    PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m.

(*
│
│          `RecursiveEscapeDestabilizes` is the caller-supplied
│          destabilization principle: unbounded recursive
│          approximation is incompatible with stable continuation. It
│          is the structural reason a stable model cannot sit at the
│          limit of an infinite nesting.
│
*)

(*                       ∀m. infinite(m) ⇒ ¬Stable(m).                        *)

Definition RecursiveEscapeDestabilizes
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (infinite : InfiniteRecursiveApproximation Model) : Prop :=
  forall m : Model,
    infinite m ->
    ~ Stable R m.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        GRADED INSTABILITY PREDICATES                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `BoundedIntrospection R bound m` says that the
│          depth-indexed penalty of `m` is bounded by `bound` at every
│          recursive depth. It is the formal room for bounded
│          self-modeling: a model may approximate at depth
│          indefinitely without growth in pressure.
│
*)

(*                     ∀d. PenaltyAtDepth(d, m) ≤ bound.                      *)

Definition BoundedIntrospection
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (bound : nat)
    (m : Model) : Prop :=
  forall depth : nat,
    PenaltyAtDepth R depth m <= bound.

(*
│
│          `StableRequiresBoundedRecursivePressure` is the boundedness
│          principle for stable continuation: every stable model
│          admits some finite bound on its depth-indexed pressure.
│          Stability is incompatible with unbounded growth across
│          recursive depth.
│
*)

(*             ∀m. Stable(m) ⇒ ∃b. ∀d. PenaltyAtDepth(d, m) ≤ b.              *)

Definition StableRequiresBoundedRecursivePressure
    (Model : Type)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall m : Model,
    Stable R m ->
    exists bound : nat,
      BoundedIntrospection Model R bound m.

(*
│
│          `ThresholdPressureAt R threshold depth m` says that the
│          depth-indexed penalty at `depth` has crossed the chosen
│          threshold. The threshold is a parameter: different choices
│          separate low pressure, fragmentation pressure, and collapse
│          pressure without identifying them.
│
*)

(*                     threshold < PenaltyAtDepth(d, m).                      *)

Definition ThresholdPressureAt
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (threshold depth : nat)
    (m : Model) : Prop :=
  threshold < PenaltyAtDepth R depth m.

(*
│
│          `AuthorityCounterPressure` is the formula-indexed surface
│          where authority meets counter-approximation. A locally
│          authoritative formula is being approximated against through
│          its negation, and some recursive depth has crossed a chosen
│          threshold. It packages the configuration that drives the
│          destabilization laws below.
│
*)

(*                     asif(m, A) ∧ approximates(m, ¬A) ∧                     *)
(*                   ∃d. threshold < PenaltyAtDepth(d, m).                    *)

Definition AuthorityCounterPressure
    (Model : Type)
    (asif : AsIFFor Model)
    (R : RecursiveApproximationStructure Model)
    (threshold : nat)
    (m : Model)
    (A : Formula) : Prop :=
  asif m A /\
  approximates R m (formula_negation A) /\
  exists depth : nat,
    ThresholdPressureAt Model R threshold depth m.

(*
│
│          `CounterCertificationAt R depth m A` records the formal
│          shape of a counter-certification attempt: the model
│          approximates against `A` through `¬A`, and that
│          counter-approximation is registered at a particular
│          recursive depth. It is an operational pressure predicate,
│          not a semantic truth predicate and not a claim that `A` is
│          metaphysically false.
│
*)

(*              approximates(m, ¬A) ∧ RecursiveDepth(m, ¬A, d).               *)

Definition CounterCertificationAt
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (depth : nat)
    (m : Model)
    (A : Formula) : Prop :=
  approximates R m (formula_negation A) /\
  RecursiveDepth R m (formula_negation A) depth.

(*
│
│          `NestedAuthorityPressure R depth m A` is the depth-indexed
│          nested version of authority-counterpressure. At a
│          particular recursive depth, the model treats `A` as locally
│          authoritative, approximates against it through `¬A`,
│          records that counter-approximation at that depth, and
│          carries positive depth-indexed pressure there. This gives
│          the API a formal hook for nested model layers without
│          introducing a concrete carrier for perceptual or
│          phenomenological contents.
│
*)

(*     asif(m, A) ∧ approximates(m, ¬A) ∧ RecursiveDepth(m, ¬A, d) ∧ 0 <      *)
(*                           PenaltyAtDepth(d, m).                            *)

Definition NestedAuthorityPressure
    (Model : Type)
    (asif : AsIFFor Model)
    (R : RecursiveApproximationStructure Model)
    (depth : nat)
    (m : Model)
    (A : Formula) : Prop :=
  asif m A /\
  approximates R m (formula_negation A) /\
  RecursiveDepth R m (formula_negation A) depth /\
  0 < PenaltyAtDepth R depth m.

(*
│
│          `UnboundedRecursivePressure` says that the depth-indexed
│          penalty eventually exceeds every finite bound. It is the
│          graded form of infinite regress and does not, by itself,
│          assert instability.
│
*)

(*                     ∀b. ∃d. b < PenaltyAtDepth(d, m).                      *)

Definition UnboundedRecursivePressure
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (m : Model) : Prop :=
  forall bound : nat,
    exists depth : nat,
      bound < PenaltyAtDepth R depth m.

(*
│
│          `UnboundedPressureDestabilizes` converts the previous
│          configuration into loss of stability: if pressure
│          eventually exceeds every finite bound, stable continuation
│          fails. This is the structural reason an embedded family
│          cannot sit at the limit of its own nesting.
│
*)

(*              ∀m. UnboundedRecursivePressure(m) ⇒ ¬Stable(m).               *)

Definition UnboundedPressureDestabilizes
    (Model : Type)
    (R : RecursiveApproximationStructure Model) : Prop :=
  forall m : Model,
    UnboundedRecursivePressure Model R m ->
    ~ Stable R m.

(*
│
│          `RecursiveCollapseAt` marks the stronger configuration in
│          which a threshold has been crossed and stability has been
│          lost. Collapse is therefore graded and explicit, not folded
│          into every approximation act.
│
*)

(*            (∃d. threshold < PenaltyAtDepth(d, m)) ∧ ¬Stable(m).            *)

Definition RecursiveCollapseAt
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (threshold : nat)
    (m : Model) : Prop :=
  (exists depth : nat,
     ThresholdPressureAt Model R threshold depth m) /\
  ~ Stable R m.

(*
│
│          `FragmentedAt R threshold m` is the partition predicate.
│          The model has crossed a depth-indexed pressure threshold
│          and is fragmented; the `Fragmented` field is the abstract
│          partitioning surface, and the definition does not commit to
│          a concrete partition carrier.
│
*)

(*          (∃d. threshold < PenaltyAtDepth(d, m)) ∧ Fragmented(m).           *)

Definition FragmentedAt
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (threshold : nat)
    (m : Model) : Prop :=
  (exists depth : nat,
     ThresholdPressureAt Model R threshold depth m) /\
  Fragmented R m.

(*
│
│          `FragmentationOrInstability R m` is the branch outcome of
│          the fragmentation laws. Under sufficient pressure, an
│          embedded model either fragments or loses stable
│          continuation. The disjunction is the layer's central
│          concession that recursive approximation need not collapse
│          into immediate inconsistency.
│
*)

(*                        Fragmented(m) ∨ ¬Stable(m).                         *)

Definition FragmentationOrInstability
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (m : Model) : Prop :=
  Fragmented R m \/ ~ Stable R m.

(*
│
│          `RecursiveFragmentationPressure R threshold` is the generic
│          fragmentation law. Any approximation act whose
│          depth-indexed penalty crosses `threshold` forces
│          fragmentation or instability. The law is parametric in the
│          threshold, so the caller decides where the branch is
│          forced.
│
*)

(*     ∀d, m, A. approximates(m, A) ∧ threshold < PenaltyAtDepth(d, m) ⇒      *)
(*                        Fragmented(m) ∨ ¬Stable(m).                         *)

Definition RecursiveFragmentationPressure
    (Model : Type)
    (R : RecursiveApproximationStructure Model)
    (threshold : nat) : Prop :=
  forall (depth : nat) (m : Model) (A : Formula),
    approximates R m A ->
    ThresholdPressureAt Model R threshold depth m ->
    FragmentationOrInstability Model R m.

(*
│
│          `AuthorityFragmentationPressure` specializes the previous
│          law to the authority-versus-approximation configuration:
│          when the model approximates against a locally authoritative
│          surface and the depth-indexed penalty crosses the
│          threshold, fragmentation or instability follows.
│
*)

(* ∀d, m, A. asif(m, A) ∧ approximates(m, ¬A) ∧ threshold < PenaltyAtDepth(d, *)
(*                                    m) ⇒                                    *)
(*                        Fragmented(m) ∨ ¬Stable(m).                         *)

Definition AuthorityFragmentationPressure
    (Model : Type)
    (asif : AsIFFor Model)
    (R : RecursiveApproximationStructure Model)
    (threshold : nat) : Prop :=
  forall (depth : nat) (m : Model) (A : Formula),
    asif m A ->
    approximates R m (formula_negation A) ->
    ThresholdPressureAt Model R threshold depth m ->
    FragmentationOrInstability Model R m.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       RECURSIVE APPROXIMATION THEOREMS                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `local_authority_counter_certification_yields_recursive_pressure`
│          is the formal counterpart of the package's "mistake"
│          reading. Local authority internalizes `A` as local
│          derivability; a counter-certification attempt against `A`
│          at recursive depth produces nested recursive pressure. The
│          theorem deliberately concludes pressure and local
│          derivability, not semantic falsity, phenomenology, or
│          collapse to `Bot`.
│
*)

(*     ModelLocalAuthority ∧ RecursiveDepthPositivePenalty ∧ asif(m,A) ∧      *)
(*               CounterCertificationAt(d,m,A) ⇒ derives(m,A) ∧               *)
(*                      NestedAuthorityPressure(d,m,A).                       *)

Theorem local_authority_counter_certification_yields_recursive_pressure :
  forall (Model : Type)
         (derives : ModelDerivability Model)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (depth : nat)
         (m : Model)
         (A : Formula),
    ModelLocalAuthority Model derives asif ->
    RecursiveDepthPositivePenalty Model R ->
    asif m A ->
    CounterCertificationAt Model R depth m A ->
    derives m A /\
    NestedAuthorityPressure Model asif R depth m A.
Proof.
  intros Model derives asif R depth m A
    Hauthority Hpositive Hasif Hcounter.
  destruct Hcounter as [Happrox Hdepth].
  split.
  - exact (Hauthority m A Hasif).
  - split.
    + exact Hasif.
    + split.
      * exact Happrox.
      * split.
        -- exact Hdepth.
        -- exact
             (Hpositive m (formula_negation A) depth Hdepth).
Qed.

(*
│
│          `nested_authority_pressure_increases_penalty_at_depth` is
│          the finite-depth accumulation step. If the caller supplies
│          the recursive authority-depth pressure law, then each
│          witnessed nested authority/counter-approximation
│          configuration at `depth` strictly increases the
│          depth-indexed penalty from `depth` to `S depth`.
│
*)

(*    RecursiveAuthorityDepthPressure ∧ NestedAuthorityPressure(d, m, A) ⇒    *)
(*               PenaltyAtDepth(d, m) < PenaltyAtDepth(d+1, m).               *)

Theorem nested_authority_pressure_increases_penalty_at_depth :
  forall (Model : Type)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (depth : nat)
         (m : Model)
         (A : Formula),
    RecursiveAuthorityDepthPressure Model asif R ->
    NestedAuthorityPressure Model asif R depth m A ->
    PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m.
Proof.
  intros Model asif R depth m A Hpressure Hnested.
  destruct Hnested as [Hasif [Happrox [_Hdepth _Hpositive]]].
  exact (Hpressure depth m A Hasif Happrox).
Qed.

(*
│
│          `strict_depth_pressure_unbounded` turns strict
│          depth-by-depth growth into unbounded recursive pressure.
│          The constructive witness for a proposed finite bound `b` is
│          depth `S b`; induction shows that strict growth at every
│          step forces `S b ≤ PenaltyAtDepth(S b, m)`.
│
*)

(*      ∀d. PenaltyAtDepth(d, m) < PenaltyAtDepth(d+1, m) ⇒ ∀b. ∃d. b <       *)
(*                           PenaltyAtDepth(d, m).                            *)

Theorem strict_depth_pressure_unbounded :
  forall (Model : Type)
         (R : RecursiveApproximationStructure Model)
         (m : Model),
    (forall depth : nat,
       PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m) ->
    UnboundedRecursivePressure Model R m.
Proof.
  intros Model R m Hstrict.
  unfold UnboundedRecursivePressure.
  intro bound.
  exists (S bound).
  assert (Htrans :
    forall a b c : nat,
      a <= b -> b <= c -> a <= c).
  {
    intros a b c Hab Hbc.
    induction Hbc as [| c Hbc IH].
    - exact Hab.
    - apply le_S. exact IH.
  }
  assert (Hfloor :
    forall depth : nat,
      depth <= PenaltyAtDepth R depth m).
  {
    intro depth.
    induction depth as [| depth IH].
    - apply le_0_n.
    - apply Htrans with
        (b := S (PenaltyAtDepth R depth m)).
      + apply le_n_S. exact IH.
      + exact (Hstrict depth).
  }
  exact (Hfloor (S bound)).
Qed.

(*
│
│          `strict_depth_pressure_obstructs_stability` is the
│          unbounded-depth obstruction. Under
│          `StableRequiresBoundedRecursivePressure`, strict pressure
│          growth at every depth contradicts stable continuation:
│          stability supplies a finite bound, while strict growth
│          exceeds that bound at some depth.
│
*)

(*    StableRequiresBoundedRecursivePressure ∧ (∀d. PenaltyAtDepth(d,m) <     *)
(*                    PenaltyAtDepth(d+1,m)) ⇒ ¬Stable(m).                    *)

Theorem strict_depth_pressure_obstructs_stability :
  forall (Model : Type)
         (R : RecursiveApproximationStructure Model)
         (m : Model),
    StableRequiresBoundedRecursivePressure Model R ->
    (forall depth : nat,
       PenaltyAtDepth R depth m < PenaltyAtDepth R (S depth) m) ->
    ~ Stable R m.
Proof.
  intros Model R m Hbounded Hstrict Hstable.
  destruct (Hbounded m Hstable) as [bound Hintro].
  destruct (strict_depth_pressure_unbounded Model R m Hstrict bound)
    as [depth Hgt].
  pose proof (Hintro depth) as Hle.
  assert (Htrans :
    forall a b c : nat,
      a <= b -> b <= c -> a <= c).
  {
    intros a b c Hab Hbc.
    induction Hbc as [| c Hbc IH].
    - exact Hab.
    - apply le_S. exact IH.
  }
  assert (Hsucc_not_le_self :
    forall a : nat,
      ~ S a <= a).
  {
    induction a as [| a IH].
    - intro H. inversion H.
    - intro H. apply IH. apply le_S_n. exact H.
  }
  apply (Hsucc_not_le_self bound).
  apply Htrans with (b := PenaltyAtDepth R depth m).
  - exact Hgt.
  - exact Hle.
Qed.

(*
│
│          `nested_authority_pressure_obstructs_stability` specializes
│          the obstruction to authority/counter-approximation at every
│          depth. If every depth carries nested authority pressure and
│          the authority-depth pressure law turns each such witness
│          into a strict increase, then stable continuation is
│          impossible under bounded-pressure stability.
│
*)

(*  RecursiveAuthorityDepthPressure ∧ (∀d. NestedAuthorityPressure(d,m,A)) ∧  *)
(*            StableRequiresBoundedRecursivePressure ⇒ ¬Stable(m).            *)

Theorem nested_authority_pressure_obstructs_stability :
  forall (Model : Type)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (m : Model)
         (A : Formula),
    RecursiveAuthorityDepthPressure Model asif R ->
    (forall depth : nat,
       NestedAuthorityPressure Model asif R depth m A) ->
    StableRequiresBoundedRecursivePressure Model R ->
    ~ Stable R m.
Proof.
  intros Model asif R m A Hpressure Hnested Hbounded.
  apply strict_depth_pressure_obstructs_stability.
  - exact Hbounded.
  - intro depth.
    exact
      (nested_authority_pressure_increases_penalty_at_depth
         Model asif R depth m A Hpressure (Hnested depth)).
Qed.

(*
│
│          `model_regulator_non_escape` is the abstract-model
│          counterpart of `regulator_non_escape`. The contradiction is
│          produced locally by model modus ponens — reabsorption gives
│          admissibility, local authority gives derivation, the
│          refutation closes the loop — and then transported outward
│          to `Sλ` by the embedding hypothesis, where `Sλ`-consistency
│          discharges it.
│
*)

(*         ModelEmbedded ∧ Sλ ⊬_Γ ⊥ ∧ ModelMP ∧ ModelLocalAuthority ∧         *)
(*                          ModelEscapeReabsorbed ∧                           *)
(*                    derives(m, ¬A) ∧ derives(m, e) ⇒ ⊥.                     *)

Theorem model_regulator_non_escape :
  forall (Model : Type)
         (Slambda : RegulatorTheory)
         (Gamma : Context)
         (derives : ModelDerivability Model)
         (asif : AsIFFor Model)
         (m : Model)
         (A escape_claim : Formula),
    ModelEmbeddedInRegulator Model Slambda Gamma derives ->
    SLambdaConsistent Slambda Gamma ->
    ModelModusPonens Model derives ->
    ModelLocalAuthority Model derives asif ->
    ModelEscapeReabsorbed Model derives asif m A escape_claim ->
    derives m (formula_negation A) ->
    derives m escape_claim ->
    False.
Proof.
  intros Model Slambda Gamma derives asif m A escape_claim
    Hembedded Hconsistent Hmp Hauthority Hescape Hrefute Hclaim.
  apply Hconsistent.
  apply Hembedded with (m := m).
  apply Hmp with (A := A).
  - exact Hrefute.
  - exact (Hauthority m A (Hescape Hclaim)).
Qed.

(*
│
│          `embedded_authority_stability_limit` is the package's
│          unifying invariant. Three facts combine:
│          regulator-admissible authority internalizes locally as
│          derivability, embedded local derivability transports
│          outward to `Sλ`, and stable continuation supplies a finite
│          bound on depth-indexed pressure. The conjunction expresses
│          that an embedded family which remains stable is one whose
│          authority surface, `Sλ` transport, and recursive pressure
│          all sit together.
│
*)

(*ModelEmbedded ∧ ModelLocalAuthority ∧ StableRequiresBoundedRecursivePressure*)
(*                         ∧ asif(m, A) ∧ Stable(m) ⇒                         *)
(*        derives(m, A) ∧ Sλ ⊢_Γ A ∧ ∃b. ∀d. PenaltyAtDepth(d, m) ≤ b.        *)

Theorem embedded_authority_stability_limit :
  forall (Model : Type)
         (Slambda : RegulatorTheory)
         (Gamma : Context)
         (derives : ModelDerivability Model)
         (asif : AsIFFor Model)
         (R : RecursiveApproximationStructure Model)
         (m : Model)
         (A : Formula),
    ModelEmbeddedInRegulator Model Slambda Gamma derives ->
    ModelLocalAuthority Model derives asif ->
    StableRequiresBoundedRecursivePressure Model R ->
    asif m A ->
    Stable R m ->
    derives m A /\
    regulator_theory_checked_derivable Slambda Gamma A /\
    exists bound : nat,
      BoundedIntrospection Model R bound m.
Proof.
  intros Model Slambda Gamma derives asif R m A
    Hembedded Hauthority Hbounded Hasif Hstable.
  pose proof (Hauthority m A Hasif) as Hlocal.
  split.
  - exact Hlocal.
  - split.
    + exact (Hembedded m A Hlocal).
    + exact (Hbounded m Hstable).
Qed.
