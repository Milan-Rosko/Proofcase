(*P002_98_QED.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / P002_98_QED                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file is the terminal proof layer of the frozen P002 development.

  The public endpoint is no longer single-equation cubic satisfiability, but
  satisfiability of finite families of cubic equations over ℕ. The proof
  surface therefore packages the external RE bridge, the family-level
  Σ₁-completeness theorem, and the conditional no-solver corollary.
  Assumption reports and extraction live in `P002_99_Artifacts`.

*)

(*
│
│          The terminal layer exports the machine semantics file
│          because the public QED statements factor through its family
│          compilers.
│
*)

(*                                P002₀₅ → QED                                *)

From P002 Require Export P002_05__Machine_Semantics.

(*
│
│          An RE-language predicate is represented abstractly as a
│          class of unary predicates over natural numbers.
│
*)

(*                          RELanguage=(ℕ→Prop)→Prop                          *)

Definition RELanguage : Type := (nat -> Prop) -> Prop.

(*
│
│          `fm_re_completeness` is the one external machine-theoretic
│          premise still needed after the cleanup: every RE language
│          has one FM program whose valid numeric trace witnesses
│          characterize exactly the language membership relation.
│
*)

(*          RE(X) ⇒ ∃ prog. ∀ n. X(n) ⇔ ∃ w. FMValidTrace(prog,n,w)           *)

Definition fm_re_completeness (RE : RELanguage) : Prop :=
  forall X,
    RE X ->
    exists prog : MachineProgram,
      forall n, X n <-> exists witness, FMValidTrace prog n witness.

(*
│
│          `cubic_family_sat_is_sigma_1_complete` is the main public
│          endpoint: every RE language reduces to satisfiability of a
│          finite family of cubic equations over one shared
│          natural-number valuation.
│
*)

(*               RE(X) ⇒ ∃ f. ∀ n. X(n) ⇔ CubicFamilyYes(f(n))                *)

Definition cubic_family_sat_is_sigma_1_complete (RE : RELanguage) : Prop :=
  forall X,
    RE X ->
    exists f : nat -> cubic_family_instance,
      forall n, X n <-> cubic_family_yes (f n).

(*
│
│          `bounded_cubic_family_sat_is_sigma_1_complete` is the
│          constructive companion endpoint: every RE language reduces
│          to the existence of some satisfiable bounded compiled
│          family. This theorem factors through the bounded compiler
│          in `P002_05__Machine_Semantics`.
│
*)

(*            RE(X) ⇒ ∃ f. ∀ n. X(n) ⇔ ∃ b. CubicFamilyYes(f(n,b))            *)

Definition bounded_cubic_family_sat_is_sigma_1_complete (RE : RELanguage) : Prop :=
  forall X,
    RE X ->
    exists f : nat -> nat -> cubic_family_instance,
      forall n, X n <-> exists bound, cubic_family_yes (f n bound).

(*
│
│          The fixed-point bridge premise isolates the external
│          no-decider input needed for the conditional no-solver
│          corollary.
│
*)

(*                 ∃ X. RE(X) ∧ ∀ solver. ¬Decides(X,solver)                  *)

Definition fixed_point_logic_bridge_premise (RE : RELanguage) : Prop :=
  exists X : nat -> Prop,
    RE X /\ forall solver : nat -> bool, ~ decides X solver.

(*
│
│          `P002_sigma1_completeness_bounded` establishes the bounded
│          family-level representation theorem. For every RE notion
│          `RE`, if `fm_re_completeness RE` holds, then every language
│          `X` in `RE` is represented by some map `f : nat -> nat ->
│          cubic_family_instance` such that `X n` holds exactly when
│          there exists a bound for which the compiled family `f n
│          bound` is satisfiable.
│
*)

(*            fmREComplete(RE) ⇒ boundedCubicFamilyΣ₁Complete(RE)             *)

Theorem P002_sigma1_completeness_bounded :
  forall RE,
    fm_re_completeness RE ->
    bounded_cubic_family_sat_is_sigma_1_complete RE.
Proof.
  intros RE Hfm X HX.
  destruct (Hfm X HX) as [prog Hprog].
  exists (fun n bound => compile_fm_family_upto prog n bound).
  intro n.
  rewrite <- compile_fm_family_exists_bound_correct.
  apply Hprog.
Qed.

(*
│
│          `P002_sigma1_completeness` establishes the unbounded
│          family-level representation theorem. For every RE notion
│          `RE`, if `fm_re_completeness RE` holds, then every language
│          `X` in `RE` is represented by some map `f : nat ->
│          cubic_family_instance` such that `X n` holds exactly when
│          the finite cubic family `f n` is satisfiable over one
│          shared valuation in `ℕ`.
│
*)

(*                fmREComplete(RE) ⇒ cubicFamilyΣ₁Complete(RE)                *)

Theorem P002_sigma1_completeness :
  forall RE,
    fm_re_completeness RE ->
    cubic_family_sat_is_sigma_1_complete RE.
Proof.
  intros RE Hfm X HX.
  destruct (Hfm X HX) as [prog Hprog].
  exists (fun n => compile_fm_family prog n).
  intro n.
  rewrite <- compile_fm_family_correct.
  apply Hprog.
Qed.

(*
│
│          `family_semantic_no_solver_from_sigma_and_bridge`
│          establishes the meta-theoretic transfer from completeness
│          to no-solver. For every RE notion `RE`, if finite
│          cubic-family satisfiability is Σ₁-complete for `RE` and if
│          `RE` contains one language with no boolean decider, then no
│          total boolean solver decides the predicate
│          `cubic_family_yes`. Equivalently: under those two premises,
│          every candidate solver for finite cubic families fails on
│          at least one family. This is a conditional theorem: it uses
│          both premises explicitly and does not claim unconditional
│          undecidability of a single cubic equation or of arbitrary
│          cubic syntax in isolation.
│
*)

(* cubicFamilyΣ₁Complete(RE) ∧ fixedPointBridge(RE) ⇒ cubicFamilyUndecidable  *)

Theorem family_semantic_no_solver_from_sigma_and_bridge :
  forall RE,
    cubic_family_sat_is_sigma_1_complete RE ->
    fixed_point_logic_bridge_premise RE ->
    cubic_family_semantic_undecidable.
Proof.
  intros RE Hsigma [X [HRE Hundec]].
  unfold cubic_family_semantic_undecidable, decides_cubic_family.
  intros solver Hsolver.
  destruct (Hsigma X HRE) as [red Hred].
  apply (Hundec (fun n => solver (red n))).
  intro n.
  rewrite Hred.
  apply Hsolver.
Qed.

(*
│
│          The main result is the unbounded family-level
│          Σ₁-completeness statement packaged as one proposition.
│
*)

(*         Main ⇔ ∀ RE. fmREComplete(RE) ⇒ cubicFamilyΣ₁Complete(RE)          *)

Definition main_result : Prop :=
  forall RE,
    fm_re_completeness RE ->
    cubic_family_sat_is_sigma_1_complete RE.

(*
│
│          The bounded main result is the bounded family-level
│          Σ₁-completeness statement packaged as one proposition.
│
*)

(*  BoundedMain ⇔ ∀ RE. fmREComplete(RE) ⇒ boundedCubicFamilyΣ₁Complete(RE)   *)

Definition bounded_main_result : Prop :=
  forall RE,
    fm_re_completeness RE ->
    bounded_cubic_family_sat_is_sigma_1_complete RE.

(*
│
│          The first corollary packages the conditional no-solver
│          theorem behind the FM-completeness and fixed-point
│          premises.
│
*)

(*      FirstCorollary ⇔ ∀ RE. fmREComplete(RE) ∧ fixedPointBridge(RE) ⇒      *)
(*                           cubicFamilyUndecidable                           *)

Definition first_corollary : Prop :=
  forall RE,
    fm_re_completeness RE ->
    fixed_point_logic_bridge_premise RE ->
    cubic_family_semantic_undecidable.

(*
│
│          `N_BoundedCubicFamilySat_RE_complete_QED` is the terminal
│          bounded certification theorem. It establishes that, for
│          every RE notion `RE`, the single premise
│          `fm_re_completeness RE` suffices to obtain bounded
│          family-level Σ₁-completeness. In other words: every
│          language in `RE` is represented by existence of some
│          satisfiable bounded finite family of cubic equations over
│          `ℕ`.
│
*)

(*         ∀ RE. fmREComplete(RE) ⇒ boundedCubicFamilyΣ₁Complete(RE)          *)

Theorem N_BoundedCubicFamilySat_RE_complete_QED : bounded_main_result.
Proof.
  exact P002_sigma1_completeness_bounded.
Qed.

(*
│
│          `N_CubicFamilySat_RE_complete_QED` is the terminal main
│          certification theorem. It establishes that, for every RE
│          notion `RE`, the single premise `fm_re_completeness RE`
│          suffices to represent every language in `RE` by
│          satisfiability of one finite family of cubic equations over
│          `ℕ` for each input. This is the precise sense in which the
│          present development proves family-level Σ₁-completeness:
│          the objects on the P002 side are finite cubic families with
│          one shared valuation, not single cubic equations.
│
*)

(*      ∀ RE. fmREComplete(RE) ⇒ ∀ X. RE(X) ⇒ ∃ f:ℕ→Family. ∀ n. X(n) ⇔       *)
(*                            CubicFamilyYes(f(n))                            *)

Theorem N_CubicFamilySat_RE_complete_QED : main_result.
Proof.
  exact P002_sigma1_completeness.
Qed.

(*
│
│          `CubicFamily_no_solver_QED` is the terminal conditional
│          no-solver corollary. It establishes that, for every RE
│          notion `RE`, if both `fm_re_completeness RE` and
│          `fixed_point_logic_bridge_premise RE` hold, then there is
│          no total boolean solver deciding `cubic_family_yes`, i.e.
│          deciding satisfiability of finite families of cubic
│          equations over one shared valuation in `ℕ`. Equivalently:
│          under those two premises, every candidate total decider
│          fails on at least one finite cubic family. This theorem
│          therefore does not say that a single cubic equation is
│          undecidable, and it does not say that “cubics” are
│          unconditionally undecidable in isolation.
│
*)

(*   ∀ RE. fmREComplete(RE) ∧ fixedPointBridge(RE) ⇒ cubicFamilyUndecidable   *)

Theorem CubicFamily_no_solver_QED : first_corollary.
Proof.
  intros RE Hfm Hbridge.
  apply (family_semantic_no_solver_from_sigma_and_bridge RE).
  - apply P002_sigma1_completeness.
    exact Hfm.
  - exact Hbridge.
Qed.
