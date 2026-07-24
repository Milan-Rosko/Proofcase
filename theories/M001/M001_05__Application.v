(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Checked MP application for regulator theories. The previous certificate layer gives us `regulator_theory_checked_derivable`; this file proves that checked derivability is closed under modus ponens by explicitly composing two finite checked proof scripts. The construction concatenates the checked proof of `A → B`, shifts every MP reference in the checked proof of `A`, and appends one final MP line for `B`.]]@*)

(*@doc.pl@[[The proof-script shifting family is internal scaffolding for application. The public layer is `regulator_theory_mp_compose` together with `regulator_theory_mp_compose_checked_lemma`, plus the checked-derivability closure lemmas for assumptions, axioms, and MP. This layer is still purely syntactic: no semantic validity, model theory, arithmetic coding, or proof search is introduced.]]@*)

(*@head.end@*)

From M001 Require Export M001_04__Certificates.

(*@section@[[PROOF-SCRIPT SHIFTING]]@*)

(*@inline@[[Concatenating two checked proof scripts changes the absolute positions of every MP reference inside the second script. `proof_script_shift_index` adds the offset; `proof_script_shift_justification` rewrites only `J_MP` indices; `proof_script_shift_line` lifts the operation to one proof line; and `proof_script_shift` maps it across a whole script.]]@*)

(*@unicodemath@[[proof_script_shift_index(k,i) ≔ k + i]]@*)
(*@unicodemath@[[proof_script_shift_justification(k, MP(i,j)) ≔ MP(k+i,k+j)]]@*)
(*@unicodemath@[[line_formula(proof_script_shift_line(k,line)) = line_formula(line)]]@*)

Definition proof_script_shift_index (offset i : nat) : nat :=
  offset + i.

Definition proof_script_shift_justification
    (offset : nat)
    (j : Justification) : Justification :=
  match j with
  | J_Assumption => J_Assumption
  | J_Axiom => J_Axiom
  | J_MP i k =>
      J_MP
        (proof_script_shift_index offset i)
        (proof_script_shift_index offset k)
  end.

Definition proof_script_shift_line
    (offset : nat)
    (line : ProofLine) : ProofLine :=
  {| line_formula := line.(line_formula);
     line_justification :=
       proof_script_shift_justification offset line.(line_justification) |}.

Definition proof_script_shift
    (offset : nat)
    (p : Proof) : Proof :=
  map (proof_script_shift_line offset) p.

Lemma proof_script_shift_length_lemma :
  forall offset p,
    length (proof_script_shift offset p) = length p.
Proof.
  intros offset p.
  unfold proof_script_shift.
  rewrite length_map.
  reflexivity.
Qed.

Lemma proof_script_shift_app_lemma :
  forall offset p q,
    proof_script_shift offset (p ++ q) =
    proof_script_shift offset p ++ proof_script_shift offset q.
Proof.
  intros offset p q.
  unfold proof_script_shift.
  rewrite map_app.
  reflexivity.
Qed.

Lemma nth_formula_proof_script_shift_lemma :
  forall offset p i F,
    nth_formula p i = Some F ->
    nth_formula (proof_script_shift offset p) i = Some F.
Proof.
  intros offset p.
  induction p as [|line p IH]; intros i F Hnth.
  - destruct i; discriminate Hnth.
  - destruct i as [|i'].
    + simpl in Hnth.
      simpl.
      exact Hnth.
    + simpl in Hnth.
      simpl.
      apply IH.
      exact Hnth.
Qed.

Lemma nth_formula_app_shifted_lemma :
  forall offset prefix p i F,
    offset = length prefix ->
    nth_formula p i = Some F ->
    nth_formula
      (prefix ++ proof_script_shift offset p)
      (offset + i) = Some F.
Proof.
  intros offset prefix p i F Hoff Hnth.
  subst offset.
  rewrite nth_formula_app_length_plus_lemma.
  apply nth_formula_proof_script_shift_lemma.
  exact Hnth.
Qed.

(*@section@[[SHIFTED CHECKING]]@*)

(*@inline@[[The shifted-checking lemmas show that a checked suffix remains checked after all of its backward MP references are moved past a checked base proof. `proof_line_valid_bool_shift_after_base_lemma` is the one-line statement; `proof_script_check_from_shift_after_base_lemma` iterates it over a script; and `proof_script_check_from_shift_after_prefix_lemma` is the form used by MP composition.]]@*)

(*@unicodemath@[[proof_script_check_from_bool(R,Γ,source_prefix,p)=true  ⇒  proof_script_check_from_bool(R,Γ,base ⧺ proof_script_shift(|base|,source_prefix),proof_script_shift(|base|,p))=true]]@*)

Lemma proof_line_valid_bool_shift_after_base_lemma :
  forall R Gamma base source_prefix line,
    proof_line_valid_bool R Gamma source_prefix line = true ->
    proof_line_valid_bool R Gamma
      (base ++ proof_script_shift (length base) source_prefix)
      (proof_script_shift_line (length base) line) = true.
Proof.
  intros R Gamma base source_prefix line Hline.
  destruct line as [phi just].
  destruct just as [| |i j].
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in Hline.
    pose proof (bool_and_true_left_lemma _ _ Hline) as Hbounds.
    pose proof (bool_and_true_right_lemma _ _ Hline) as Hmp.
    pose proof (bool_and_true_left_lemma _ _ Hbounds) as Hi.
    pose proof (bool_and_true_right_lemma _ _ Hbounds) as Hj.
    simpl.
    unfold proof_script_shift_index.
    assert (Hlt_i :
      Nat.ltb (length base + i)
        (length base + length source_prefix) = true).
    {
      apply Nat.ltb_lt.
      apply Nat.add_lt_mono_l.
      apply Nat.ltb_lt.
      exact Hi.
    }
    assert (Hlt_j :
      Nat.ltb (length base + j)
        (length base + length source_prefix) = true).
    {
      apply Nat.ltb_lt.
      apply Nat.add_lt_mono_l.
      apply Nat.ltb_lt.
      exact Hj.
    }
    rewrite length_app.
    rewrite proof_script_shift_length_lemma.
    rewrite Hlt_i.
    rewrite Hlt_j.
    simpl.
    apply mp_valid_bool_components_lemma in Hmp.
    destruct Hmp as [C [[HiF HjF] | [HiF HjF]]].
    + apply mp_valid_bool_direct_lemma with (C := C).
      * apply nth_formula_app_shifted_lemma; reflexivity || exact HiF.
      * apply nth_formula_app_shifted_lemma; reflexivity || exact HjF.
    + apply mp_valid_bool_reverse_lemma with (C := C).
      * apply nth_formula_app_shifted_lemma; reflexivity || exact HiF.
      * apply nth_formula_app_shifted_lemma; reflexivity || exact HjF.
Qed.

Lemma proof_script_check_from_shift_after_base_lemma :
  forall R Gamma base source_prefix p,
    proof_script_check_from_bool R Gamma source_prefix p = true ->
    proof_script_check_from_bool R Gamma
      (base ++ proof_script_shift (length base) source_prefix)
      (proof_script_shift (length base) p) = true.
Proof.
  intros R Gamma base source_prefix p.
  revert source_prefix.
  induction p as [|line p IH]; intros source_prefix Hcheck.
  - reflexivity.
  - simpl in Hcheck.
    pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hline.
    pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hrest.
    simpl.
    rewrite (proof_line_valid_bool_shift_after_base_lemma
      R Gamma base source_prefix line Hline).
    simpl.
    replace
      ((base ++ proof_script_shift (length base) source_prefix) ++
       cons (proof_script_shift_line (length base) line) nil)
      with
      (base ++
       proof_script_shift (length base)
         (source_prefix ++ cons line nil)).
    + apply IH.
      exact Hrest.
    + rewrite proof_script_shift_app_lemma.
      simpl.
      rewrite app_assoc.
      reflexivity.
Qed.

Lemma proof_script_check_from_shift_after_prefix_lemma :
  forall R Gamma prefix p,
    proof_script_check_from_bool R Gamma nil prefix = true ->
    proof_script_check_from_bool R Gamma nil p = true ->
    proof_script_check_from_bool R Gamma prefix
      (proof_script_shift (length prefix) p) = true.
Proof.
  intros R Gamma prefix p _ Hp.
  rewrite <- (app_nil_r prefix) at 1.
  exact
    (proof_script_check_from_shift_after_base_lemma
      R Gamma prefix nil p Hp).
Qed.

(*@section@[[MP PROOF-SCRIPT COMPOSITION]]@*)

(*@inline@[[`proof_script_last_index p` is the position of the final line of `p`. `regulator_theory_mp_compose B p_imp p_arg` concatenates the checked proof of `A → B`, the shifted checked proof of `A`, and one final MP line proving `B`.]]@*)

(*@unicodemath@[[last_index(p) ≔ |p| - 1]]@*)
(*@unicodemath@[[regulator_theory_mp_compose(B,p_imp,p_arg) ≔ p_imp ⧺ proof_script_shift(|p_imp|,p_arg) ⧺ MP(B,last_index(p_imp),|p_imp|+last_index(p_arg))]]@*)

Definition proof_script_last_index (p : Proof) : nat :=
  pred (length p).

Definition regulator_theory_mp_compose
    (B : Formula)
    (p_imp p_arg : Proof) : Proof :=
  let offset := length p_imp in
  let shifted_arg := proof_script_shift offset p_arg in
  (p_imp ++ shifted_arg) ++
    cons
      (pl_mp B
        (proof_script_last_index p_imp)
        (offset + proof_script_last_index p_arg))
      nil.

Lemma last_formula_some_last_index_lemma :
  forall p F,
    last_formula p = Some F ->
    nth_formula p (proof_script_last_index p) = Some F.
Proof.
  induction p as [|line p IH]; intros F Hlast.
  - discriminate Hlast.
  - destruct p as [|line' p'].
    + simpl in Hlast.
      inversion Hlast.
      reflexivity.
    + simpl in Hlast.
      unfold proof_script_last_index.
      simpl.
      fold (proof_script_last_index (cons line' p')).
      apply IH.
      exact Hlast.
Qed.

Lemma nth_formula_app_shifted_last_lemma :
  forall prefix p offset F,
    offset = length prefix ->
    last_formula p = Some F ->
    nth_formula
      (prefix ++ proof_script_shift offset p)
      (offset + proof_script_last_index p) = Some F.
Proof.
  intros prefix p offset F Hoff Hlast.
  apply nth_formula_app_shifted_lemma.
  - exact Hoff.
  - apply last_formula_some_last_index_lemma.
    exact Hlast.
Qed.

(*@section@[[CHECKED MP COMPOSITION]]@*)

(*@inline@[[`regulator_theory_mp_compose_checked_lemma` is the central theorem of this file: composing checked scripts for `A → B` and `A` produces a checked script for `B`. The proof shifts the argument script after the implication script, verifies the concatenated prefix, reads both final formulas back by index, and checks the final MP line.]]@*)

(*@unicodemath@[[R; Γ ⊢check[p_imp] A → B  ∧  R; Γ ⊢check[p_arg] A  ⇒  R; Γ ⊢check[regulator_theory_mp_compose(B,p_imp,p_arg)] B]]@*)

Lemma regulator_theory_mp_compose_checked_lemma :
  forall R Gamma A B p_imp p_arg,
    regulator_theory_check_bool R Gamma p_imp (Imp A B) = true ->
    regulator_theory_check_bool R Gamma p_arg A = true ->
    regulator_theory_check_bool R Gamma
      (regulator_theory_mp_compose B p_imp p_arg)
      B = true.
Proof.
  intros R Gamma A B p_imp p_arg Himp Harg.
  pose proof (regulator_theory_check_true_lines_lemma R Gamma p_imp (Imp A B) Himp)
    as Himp_lines.
  pose proof (regulator_theory_check_true_lines_lemma R Gamma p_arg A Harg)
    as Harg_lines.
  pose proof (regulator_theory_check_true_last_lemma R Gamma p_imp (Imp A B) Himp)
    as Himp_last.
  pose proof (regulator_theory_check_true_last_lemma R Gamma p_arg A Harg)
    as Harg_last.
  unfold regulator_theory_mp_compose.
  set (shifted_arg := proof_script_shift (length p_imp) p_arg).
  set (base := p_imp ++ shifted_arg).
  assert (Harg_shift :
    proof_script_check_from_bool R Gamma p_imp shifted_arg = true).
  {
    unfold shifted_arg.
    apply proof_script_check_from_shift_after_prefix_lemma.
    - exact Himp_lines.
    - exact Harg_lines.
  }
  assert (Hbase :
    proof_script_check_from_bool R Gamma nil base = true).
  {
    unfold base.
    apply proof_script_check_append_true_lemma.
    - exact Himp_lines.
    - exact Harg_shift.
  }
  assert (Hnth_imp :
    nth_formula base (proof_script_last_index p_imp) =
    Some (Imp A B)).
  {
    unfold base.
    apply nth_formula_app_left_lemma.
    apply last_formula_some_last_index_lemma.
    exact Himp_last.
  }
  assert (Hnth_arg :
    nth_formula base (length p_imp + proof_script_last_index p_arg) =
    Some A).
  {
    unfold base, shifted_arg.
    apply nth_formula_app_shifted_last_lemma.
    - reflexivity.
    - exact Harg_last.
  }
  assert (Hline :
    proof_line_valid_bool R Gamma base
      (pl_mp B
        (proof_script_last_index p_imp)
        (length p_imp + proof_script_last_index p_arg)) = true).
  {
    unfold proof_line_valid_bool.
    simpl.
    rewrite (nth_formula_some_ltb_lemma _ _ _ Hnth_imp).
    rewrite (nth_formula_some_ltb_lemma _ _ _ Hnth_arg).
    simpl.
    apply mp_valid_bool_reverse_lemma with (C := A).
    - exact Hnth_imp.
    - exact Hnth_arg.
  }
  assert (Hfinal_block :
    proof_script_check_from_bool R Gamma base
      (cons
        (pl_mp B
          (proof_script_last_index p_imp)
          (length p_imp + proof_script_last_index p_arg))
        nil) = true).
  {
    simpl.
    rewrite Hline.
    reflexivity.
  }
  assert (Hfull_lines :
    proof_script_check_from_bool R Gamma nil
      (base ++
        cons
          (pl_mp B
            (proof_script_last_index p_imp)
            (length p_imp + proof_script_last_index p_arg))
          nil) = true).
  {
    apply proof_script_check_append_true_lemma.
    - exact Hbase.
    - exact Hfinal_block.
  }
  unfold regulator_theory_check_bool.
  rewrite Hfull_lines.
  simpl.
  rewrite last_formula_app_single_lemma.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

(*@section@[[CHECKED-DERIVABILITY APPLICATION]]@*)

(*@inline@[[The derivability-level MP lemma forgets the two source scripts after composing them. This is the existential closure form consumed by the later inductive-adequacy and regulator-closure layers: checked derivability is closed under object-level modus ponens because the scripts themselves can be concatenated and re-indexed.]]@*)

(*@unicodemath@[[R; Γ ⊢check A → B  ∧  R; Γ ⊢check A  ⇒  R; Γ ⊢check B]]@*)

Lemma regulator_theory_checked_derivable_mp_lemma :
  forall R Gamma A B,
    regulator_theory_checked_derivable R Gamma (Imp A B) ->
    regulator_theory_checked_derivable R Gamma A ->
    regulator_theory_checked_derivable R Gamma B.
Proof.
  intros R Gamma A B Himp Harg.
  destruct Himp as [p_imp Hp_imp].
  destruct Harg as [p_arg Hp_arg].
  exists (regulator_theory_mp_compose B p_imp p_arg).
  apply regulator_theory_mp_compose_checked_lemma with (A := A);
    assumption.
Qed.

(*@inline@[[One-line assumption and axiom scripts witness the base cases for checked derivability. They are deliberately small: a context member is checked by `J_Assumption`, and an available axiom is checked by `J_Axiom`.]]@*)

(*@unicodemath@[[A ∈ Γ  ⇒  R; Γ ⊢check A]]@*)

Lemma regulator_theory_assumption_checked_derivable_lemma :
  forall R Gamma A,
    ctx_mem_bool A Gamma = true ->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A Hmem.
  exists (cons (pl_assumption A) nil).
  unfold regulator_theory_check_bool,
    proof_script_check_from_bool,
    proof_line_valid_bool,
    pl_assumption.
  simpl.
  rewrite Hmem.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

(*@unicodemath@[[available_axiom_bool(R,A)=true  ⇒  R; Γ ⊢check A]]@*)

Lemma regulator_theory_axiom_checked_derivable_lemma :
  forall R Gamma A,
    available_axiom_bool R A = true ->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A Haxiom.
  exists (cons (pl_axiom A) nil).
  unfold regulator_theory_check_bool,
    proof_script_check_from_bool,
    proof_line_valid_bool,
    pl_axiom.
  simpl.
  rewrite Haxiom.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.
