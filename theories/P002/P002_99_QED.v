(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This file is the terminal certification layer of the reset P002 development.]]@*)

(*@doc.pl@[[The public endpoint is no longer single-equation cubic satisfiability, but satisfiability of finite families of cubic equations over ℕ. The certification surface therefore packages the external RE bridge, the family-level Σ₁-completeness theorem, and the semantic undecidability corollary in one terminal file.]]@*)

(*@head.end@*)

From P002 Require Export P002_10__Machine_Semantics.

Definition RELanguage : Type := (nat -> Prop) -> Prop.

Definition fm_re_completeness (RE : RELanguage) : Prop :=
  forall X,
    RE X ->
    exists prog : MachineProgram,
      forall n, X n <-> exists witness, FMValidTrace prog n witness.

Definition cubic_family_sat_is_sigma_1_complete (RE : RELanguage) : Prop :=
  forall X,
    RE X ->
    exists f : nat -> cubic_family_instance,
      forall n, X n <-> cubic_family_yes (f n).

Definition bounded_cubic_family_sat_is_sigma_1_complete (RE : RELanguage) : Prop :=
  forall X,
    RE X ->
    exists f : nat -> nat -> cubic_family_instance,
      forall n, X n <-> exists bound, cubic_family_yes (f n bound).

Definition fixed_point_logic_bridge_premise (RE : RELanguage) : Prop :=
  exists X : nat -> Prop,
    RE X /\ forall solver : nat -> bool, ~ decides X solver.

(*@inline@[[`fm_re_completeness` is the one external machine-theoretic premise still needed after the cleanup: every RE language admits one FM program whose valid numeric trace witnesses characterize exactly the language membership relation.]]@*)
(*@inline@[[`cubic_family_sat_is_sigma_1_complete` is the main public endpoint: every RE language reduces to satisfiability of a finite family of cubic equations over one shared natural-number valuation.]]@*)
(*@inline@[[`bounded_cubic_family_sat_is_sigma_1_complete` is the constructive companion endpoint: every RE language reduces to the existence of some satisfiable bounded compiled family. This theorem factors entirely through the syntax-driven bounded search layer in `P002_10`.]]@*)

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

(*@inline@[[`P002_sigma1_completeness_bounded` is the constructive outer bridge: once the external FM witness-completeness premise is supplied, the bounded compiler family already realizes the full RE reduction without any classical search collapse.]]@*)
(*@unicodemath@[[fm\_re\_completeness(RE)\Rightarrow bounded\_cubic\_family\_sat\_is\_\sigma_1\_complete(RE).]]@*)

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

(*@inline@[[`P002_sigma1_completeness` is the unbounded closure theorem. Relative to the bounded result above, its extra strength comes only from packaging the outer existential over bounds into one family-valued map via the classical open search layer.]]@*)
(*@unicodemath@[[fm\_re\_completeness(RE)\Rightarrow cubic\_family\_sat\_is\_\sigma_1\_complete(RE).]]@*)

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

(*@inline@[[The family-level no-solver endpoint is the direct classical consequence of Σ₁-completeness plus one undecidable RE language. No extra certification shim is needed anymore.]]@*)
(*@inline@[[`family_semantic_no_solver_from_sigma_and_bridge` is the terminal meta-theoretic discharge: once a single undecidable RE language is provided, the family-level completeness theorem converts it into semantic undecidability of cubic-family satisfiability.]]@*)
(*@unicodemath@[[cubic\_family\_sat\_is\_\sigma_1\_complete(RE)\wedge fixed\_point\_logic\_bridge\_premise(RE)\Rightarrow cubic\_family\_semantic\_undecidable.]]@*)

Definition main_result : Prop :=
  forall RE,
    fm_re_completeness RE ->
    cubic_family_sat_is_sigma_1_complete RE.

Definition bounded_main_result : Prop :=
  forall RE,
    fm_re_completeness RE ->
    bounded_cubic_family_sat_is_sigma_1_complete RE.

Definition first_corollary : Prop :=
  forall RE,
    fm_re_completeness RE ->
    fixed_point_logic_bridge_premise RE ->
    cubic_family_semantic_undecidable.

(*@inline@[[CONSTRUCTIVE COMPANION. Every RE language also reduces to the existence of some satisfiable bounded compiled family. This is the syntax-driven bounded theorem with no extra classical search collapse.]]@*)
Theorem N_BoundedCubicFamilySat_RE_complete_QED : bounded_main_result.
Proof.
  exact P002_sigma1_completeness_bounded.
Qed.

(*@inline@[[This bounded QED endpoint is the cleanest certified core of the reset project. Its assumption report is closed under the global context, so it marks the exact frontier of what the current syntax-driven pipeline establishes without any classical witness-choice layer.]]@*)
(*@unicode@[[\forall RE,\ fm\_re\_completeness(RE)\Rightarrow bounded\_cubic\_family\_sat\_is\_\sigma_1\_complete(RE).]]@*)

(*@inline@[[MAIN RESULT. Satisfiability of finite cubic families over ℕ is Σ₁-complete, provided the external FM witness bridge is supplied.]]@*)
Theorem N_CubicFamilySat_RE_complete_QED : main_result.
Proof.
  exact P002_sigma1_completeness.
Qed.

(*@inline@[[COROLLARY. The same bridge, together with one undecidable RE language, yields semantic undecidability of cubic-family satisfiability.]]@*)
Theorem CubicFamily_no_solver_QED : first_corollary.
Proof.
  intros RE Hfm Hbridge.
  apply (family_semantic_no_solver_from_sigma_and_bridge RE).
  - apply P002_sigma1_completeness.
    exact Hfm.
  - exact Hbridge.
Qed.

Redirect "theories/P002/appendix/assumptions/N_CubicFamilySat_RE_complete_QED.txt"
  Print Assumptions N_CubicFamilySat_RE_complete_QED.

Redirect "theories/P002/appendix/assumptions/CubicFamily_no_solver_QED.txt"
  Print Assumptions CubicFamily_no_solver_QED.

Redirect "theories/P002/appendix/assumptions/N_BoundedCubicFamilySat_RE_complete_QED.txt"
  Print Assumptions N_BoundedCubicFamilySat_RE_complete_QED.
