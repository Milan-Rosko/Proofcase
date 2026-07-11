(*A002_02__Normalization.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / A002_02__Normalization                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Normalization and verification layer for A002-Core. We retain the
  arithmetic verifier surface, package its certificates and basic theorems,
  and provide an inductive normal form on which effectivity can be checked
  without materializing nested A001 codes.

  The first half of this file preserves the original A001-coded verifier as
  an extraction and compatibility surface. Its certificate checker
  deliberately reruns that verifier and therefore establishes agreement, not
  an independent logical soundness theorem. The second half is the
  effectivity boundary: formulas, rules, lines, and derivations are
  normalized to inductive data, checked structurally, and related to
  independent inductive validity judgments by two reflection theorems.

*)

From A002 Require Export A002_01__Hilbert_Syntax_Checkers.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          LOCAL CERTIFICATE PAYLOADS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `code_local_cert j checked_rule` records that line `j` was
│          accepted by a local rule checker whose successful payload
│          is `checked_rule`. The payload itself is already of the
│          form `encode rule data`.
│
*)

(*          code_local_cert_payload(j,checked) ≔ encode(j,checked).           *)

Definition code_local_cert_payload (j checked_rule : nat) : nat :=
  encode j checked_rule.

(*
│
│          `code_final_cert_payload` records the claimed length,
│          target, local certificate list, and final displayed
│          formula. The local list is accumulated in reverse
│          verification order by the core loop.
│
*)

(*code_final_cert_payload(n,θ,certs,φ) ≔ encode(n,encode(θ,encode(certs,φ))). *)

Definition code_final_cert_payload
  (n theta certs final_formula : nat)
  : nat :=
  encode n (encode theta (encode certs final_formula)).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                LINE DISPATCH                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `verify_line n body j` fetches line `j`, checks its
│          canonical line shape and rule tag, dispatches to the
│          corresponding rule checker, and returns the local
│          certificate payload on success.
│
*)

(*            verify_line(n,body,j)=accept(encode(j,checked_rule))            *)
(*  ⇔ line j is fetchable and its selected K, S, or MP checker accepts with   *)
(*                           payload checked_rule.                            *)

Definition verify_line (n body j : nat) : nat :=
  let fetched := nth_line n body j in
  if acceptedb fetched then
    let ell := result_payload fetched in
    if canonical001b ell then
      let tag := line_tag ell in
      let phi := line_formula ell in
      let parsed_tag := parse_rule_tag tag in
      if acceptedb parsed_tag then
        let tag_payload := result_payload parsed_tag in
        let rule := fst001 tag_payload in
        let payload := snd001 tag_payload in
        if Nat.eqb rule RULE_AXK then
          let checked := check_axk phi in
          if acceptedb checked then
            accept (code_local_cert_payload j (result_payload checked))
          else
            reject STAGE_RULE j (result_payload checked)
        else if Nat.eqb rule RULE_AXS then
          let checked := check_axs phi in
          if acceptedb checked then
            accept (code_local_cert_payload j (result_payload checked))
          else
            reject STAGE_RULE j (result_payload checked)
        else if Nat.eqb rule RULE_MP then
          if canonical001b payload then
            let p := fst001 payload in
            let q := snd001 payload in
            let checked := check_mp n body j p q in
            if acceptedb checked then
              accept (code_local_cert_payload j (result_payload checked))
            else
              reject STAGE_RULE j (result_payload checked)
          else
            reject STAGE_TAG j ERR_NONCANONICAL_NODE
        else
          reject STAGE_TAG j ERR_UNKNOWN_RULE
      else
        reject STAGE_TAG j (result_payload parsed_tag)
    else
      reject STAGE_LINE j ERR_NONCANONICAL_LINE
  else
    reject STAGE_LINE j (result_payload fetched).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              BOUNDED LINE LOOP                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `verify_lines fuel n body j certs` checks lines `j` through
│          `n - 1`, consuming one unit of fuel per line. The
│          accumulator `certs` is a tagged list of local certificates.
│
*)

  The loop invariant is operational: indices below `j` have already been
  checked, and `certs` contains their local certificates in reverse order. If
  `j = n`, the accumulator is accepted immediately; otherwise one successful
  line extends the accumulator and advances both the index and the structural
  recursion.

(*              verify_lines(fuel,n,body,n,certs)=accept(certs).              *)

Fixpoint verify_lines
  (fuel n body j certs : nat)
  : nat :=
  match fuel with
  | 0 =>
      if Nat.eqb j n then
        accept certs
      else
        reject STAGE_RULE j ERR_FUEL_EXHAUSTED
  | S fuel' =>
      if Nat.eqb j n then
        accept certs
      else
        let checked := verify_line n body j in
        if acceptedb checked then
          let local_cert := result_payload checked in
          verify_lines fuel' n body (S j) (code_cons local_cert certs)
        else
          checked
  end.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               FINAL CONCLUSION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `final_formula_result n body` fetches the last line of a
│          nonempty derivation and returns its displayed formula. It
│          is used only after the bounded line loop has accepted.
│
*)

(*       final_formula_result(n,body)=accept(φ) ⇒ body[n-1] displays φ.       *)

Definition final_formula_result (n body : nat) : nat :=
  let last := Nat.pred n in
  let fetched := nth_line n body last in
  if acceptedb fetched then
    let parsed := parse_line (result_payload fetched) in
    if acceptedb parsed then
      accept (parsed_line_formula (result_payload parsed))
    else
      reject STAGE_CONCLUSION last (result_payload parsed)
  else
    reject STAGE_CONCLUSION last (result_payload fetched).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                MAIN VERIFIER                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `A002_Verify d theta` checks the canonical derivation
│          header, exact body length, every local line, and final
│          conclusion equality against `theta`. Success returns
│          `accept p`; failure returns the first deterministic
│          arithmetic error.
│
*)

  Verification proceeds in a fixed order: canonical header, exact tagged-list
  length, non-emptiness, local line loop, final-line retrieval, and target
  equality. This ordering makes rejection deterministic and assigns every
  failure to the earliest applicable stage.

(*       A002_Verify(d,θ)=accept(code_final_cert_payload(n,θ,certs,θ))        *)
(*⇒ d has exact length n>0, every line checks, and its final displayed formula*)
(*                                   is θ.                                    *)

Definition A002_Verify (d theta : nat) : nat :=
  if canonical001b d then
    let n := fst001 d in
    let body := snd001 d in
    if list_exact_lengthb n body then
      if Nat.eqb n 0 then
        reject STAGE_CONCLUSION 0 ERR_EMPTY_DERIVATION
      else
        let checked_lines := verify_lines n n body 0 code_nil in
        if acceptedb checked_lines then
          let certs := result_payload checked_lines in
          let final_formula := final_formula_result n body in
          if acceptedb final_formula then
            let phi_last := result_payload final_formula in
            if Nat.eqb phi_last theta then
              accept (code_final_cert_payload n theta certs phi_last)
            else
              reject STAGE_CONCLUSION (Nat.pred n) ERR_BAD_CONCLUSION
          else
            final_formula
        else
          checked_lines
    else
      reject STAGE_LIST_STRUCTURE 0 ERR_BAD_DERIVATION_LENGTH
  else
    reject STAGE_DERIVATION_HEADER 0 ERR_NONCANONICAL_DERIVATION.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               BASIC LOOP FACTS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          At the end index, the bounded verifier loop accepts the
│          accumulated certificate list without inspecting fuel beyond
│          the guard.
│
*)

(*  ∀ fuel,n,body,certs, verify_lines(S fuel,n,body,n,certs)=accept(certs).   *)

Lemma verify_lines_at_end :
  forall fuel n body certs,
    verify_lines (S fuel) n body n certs = accept certs.
Proof.
  intros fuel n body certs.
  cbn [verify_lines].
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*
│
│          The main verifier is a deterministic function. This theorem
│          is included here as the computational determinism fact; the
│          exported soundness layer may re-export it.
│
*)

(*             A002_Verify(d,θ)=r₁ ∧ A002_Verify(d,θ)=r₂ ⇒ r₁=r₂.             *)

Theorem A002_Verify_deterministic :
  forall d theta r1 r2,
    A002_Verify d theta = r1 ->
    A002_Verify d theta = r2 ->
    r1 = r2.
Proof.
  intros d theta r1 r2 H1 H2.
  rewrite <- H1.
  exact H2.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           ARITHMETIC CERTIFICATES                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `code_local_cert j rule payload` is the expanded
│          constructor for a local certificate: the checked line index
│          is paired with the rule code and its rule-specific evidence
│          payload.
│
*)

(*     code_local_cert(j,rule,payload) ≔ encode(j,encode(rule,payload)).      *)

Definition code_local_cert (j rule payload : nat) : nat :=
  encode j (encode rule payload).

(*
│
│          `code_local_cert_from_checked` names the exact packed form
│          emitted by `verify_line`, where the local rule checker has
│          already combined its rule code and evidence.
│
*)

Definition code_local_cert_from_checked (j checked_rule : nat) : nat :=
  code_local_cert_payload j checked_rule.

(*
│
│          `local_cert_index` projects the verified line index from a
│          local certificate code.
│
*)

Definition local_cert_index (cert : nat) : nat :=
  fst001 cert.

(*
│
│          `local_cert_rule_payload` projects the packed rule/evidence
│          component from a local certificate.
│
*)

Definition local_cert_rule_payload (cert : nat) : nat :=
  snd001 cert.

(*
│
│          `local_cert_rule` projects the numerical K, S, or MP rule
│          code from the packed local certificate payload.
│
*)

Definition local_cert_rule (cert : nat) : nat :=
  fst001 (local_cert_rule_payload cert).

(*
│
│          `local_cert_payload` projects the rule-specific evidence
│          stored beneath the local rule code.
│
*)

Definition local_cert_payload (cert : nat) : nat :=
  snd001 (local_cert_rule_payload cert).

(*
│
│          `code_global_cert` gives a stable public name to the final
│          verifier payload containing length, target, reversed local
│          certificates, and final displayed formula.
│
*)

Definition code_global_cert
  (n theta certs final_formula : nat)
  : nat :=
  code_final_cert_payload n theta certs final_formula.

(*
│
│          The first projection of a global certificate is its claimed
│          derivation length.
│
*)

Definition cert_length (p : nat) : nat :=
  fst001 p.

(*
│
│          `cert_tail` exposes the packed
│          target/local-list/final-formula remainder of a global
│          certificate.
│
*)

Definition cert_tail (p : nat) : nat :=
  snd001 p.

(*
│
│          `cert_target` projects the target formula recorded when the
│          verifier accepted.
│
*)

Definition cert_target (p : nat) : nat :=
  fst001 (cert_tail p).

(*
│
│          `cert_body` projects the pair containing the reversed local
│          certificate list and final displayed formula.
│
*)

Definition cert_body (p : nat) : nat :=
  snd001 (cert_tail p).

(*
│
│          `cert_local_list` projects the tagged arithmetic list
│          accumulated by the bounded line loop.
│
*)

Definition cert_local_list (p : nat) : nat :=
  fst001 (cert_body p).

(*
│
│          `cert_final_formula` projects the final formula
│          independently recorded in the accepted payload.
│
*)

Definition cert_final_formula (p : nat) : nat :=
  snd001 (cert_body p).

(*
│
│          `A002_Certb d theta p` is a generated-certificate agreement
│          check: it reruns `A002_Verify d theta` and compares the
│          complete result with `accept p`. It is not a
│          decompositional replay checker.
│
*)

(*             A002_Certb(d,θ,p) ≔ (A002_Verify(d,θ)=?accept(p)).             *)

Definition A002_Certb (d theta p : nat) : bool :=
  Nat.eqb (A002_Verify d theta) (accept p).

(*
│
│          Any payload returned by the verifier is accepted by the
│          generated-certificate agreement check.
│
*)

Lemma A002_Certb_of_verify :
  forall d theta p,
    A002_Verify d theta = accept p ->
    A002_Certb d theta p = true.
Proof.
  intros d theta p Hverify.
  unfold A002_Certb.
  rewrite Hverify.
  apply Nat.eqb_refl.
Qed.

(*
│
│          The global certificate constructor exposes its length field
│          through `cert_length`.
│
*)

(*               cert_length(code_global_cert(n,θ,certs,φ))=n.                *)

Lemma cert_length_code_global_cert :
  forall n theta certs final_formula,
    cert_length (code_global_cert n theta certs final_formula) = n.
Proof.
  intros n theta certs final_formula.
  unfold cert_length, code_global_cert, code_final_cert_payload.
  apply fst001_encode.
Qed.

(*
│
│          The global certificate constructor exposes its recorded
│          target through `cert_target`.
│
*)

(*               cert_target(code_global_cert(n,θ,certs,φ))=θ.                *)

Lemma cert_target_code_global_cert :
  forall n theta certs final_formula,
    cert_target (code_global_cert n theta certs final_formula) = theta.
Proof.
  intros n theta certs final_formula.
  unfold cert_target, cert_tail, code_global_cert, code_final_cert_payload.
  rewrite snd001_encode.
  apply fst001_encode.
Qed.

(*
│
│          The global certificate constructor exposes the accumulated
│          local certificate list through `cert_local_list`.
│
*)

(*           cert_local_list(code_global_cert(n,θ,certs,φ))=certs.            *)

Lemma cert_local_list_code_global_cert :
  forall n theta certs final_formula,
    cert_local_list (code_global_cert n theta certs final_formula) = certs.
Proof.
  intros n theta certs final_formula.
  unfold cert_local_list, cert_body, cert_tail, code_global_cert,
    code_final_cert_payload.
  rewrite snd001_encode.
  rewrite snd001_encode.
  apply fst001_encode.
Qed.

(*
│
│          The global certificate constructor exposes its final
│          displayed formula through `cert_final_formula`.
│
*)

(*            cert_final_formula(code_global_cert(n,θ,certs,φ))=φ.            *)

Lemma cert_final_formula_code_global_cert :
  forall n theta certs final_formula,
    cert_final_formula (code_global_cert n theta certs final_formula) =
    final_formula.
Proof.
  intros n theta certs final_formula.
  unfold cert_final_formula, cert_body, cert_tail, code_global_cert,
    code_final_cert_payload.
  rewrite snd001_encode.
  rewrite snd001_encode.
  apply snd001_encode.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           ARITHMETIC SURFACE FACTS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Arithmetic verifier acceptance implies agreement with the
│          generated-certificate checker. This theorem certifies
│          result consistency, while logical schema validity is
│          handled by the normalized reflection theorems below.
│
*)

Theorem verify_accept_sound :
  forall d theta p,
    A002_Verify d theta = encode 1 p ->
    A002_Certb d theta p = true.
Proof.
  intros d theta p Hverify.
  apply A002_Certb_of_verify.
  unfold accept.
  cbn [STATUS_ACCEPT].
  exact Hverify.
Qed.

(*
│
│          The artifact-facing generated-certificate theorem restates
│          the same agreement fact under its public report name.
│
*)

Theorem generated_cert_checks :
  forall d theta p,
    A002_Verify d theta = encode 1 p ->
    A002_Certb d theta p = true.
Proof.
  intros d theta p Hverify.
  apply verify_accept_sound.
  exact Hverify.
Qed.

(*
│
│          The exported determinism theorem gives the computational
│          uniqueness fact a stable public name.
│
*)

Theorem A002_Verify_deterministic_export :
  forall d theta r1 r2,
    A002_Verify d theta = r1 ->
    A002_Verify d theta = r2 ->
    r1 = r2.
Proof.
  apply A002_Verify_deterministic.
Qed.

(*
│
│          The arithmetic K checker shape lemma records the status and
│          payload projections forced by an assumed accepted result.
│          It does not invert the K schema; normalized reflection
│          performs that stronger task.
│
*)

Lemma check_axk_sound :
  forall phi cert,
    check_axk phi = encode 1 cert ->
    result_status (check_axk phi) = STATUS_ACCEPT /\
    result_payload (check_axk phi) = cert.
Proof.
  intros phi cert Hcheck.
  split.
  - rewrite Hcheck.
    unfold result_status.
    rewrite fst001_encode.
    reflexivity.
  - rewrite Hcheck.
    unfold result_payload.
    rewrite snd001_encode.
    reflexivity.
Qed.

(*
│
│          The corresponding S checker shape lemma exposes the
│          accepted status and reported certificate payload.
│
*)

Lemma check_axs_sound :
  forall phi cert,
    check_axs phi = encode 1 cert ->
    result_status (check_axs phi) = STATUS_ACCEPT /\
    result_payload (check_axs phi) = cert.
Proof.
  intros phi cert Hcheck.
  split.
  - rewrite Hcheck.
    unfold result_status.
    rewrite fst001_encode.
    reflexivity.
  - rewrite Hcheck.
    unfold result_payload.
    rewrite snd001_encode.
    reflexivity.
Qed.

(*
│
│          The MP checker shape lemma exposes the accepted status and
│          payload under an assumed arithmetic acceptance equation.
│
*)

Lemma check_mp_sound :
  forall n body j p q cert,
    check_mp n body j p q = encode 1 cert ->
    result_status (check_mp n body j p q) = STATUS_ACCEPT /\
    result_payload (check_mp n body j p q) = cert.
Proof.
  intros n body j p q cert Hcheck.
  split.
  - rewrite Hcheck.
    unfold result_status.
    rewrite fst001_encode.
    reflexivity.
  - rewrite Hcheck.
    unfold result_payload.
    rewrite snd001_encode.
    reflexivity.
Qed.

(*
│
│          The exported fuel guard restates that reaching the end
│          index dominates the positive-fuel branch and accepts the
│          accumulated certificates immediately.
│
*)

Lemma verify_lines_no_fuel_failure_at_end :
  forall fuel n body certs,
    verify_lines (S fuel) n body n certs = accept certs.
Proof.
  apply verify_lines_at_end.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            INDUCTIVE NORMAL FORM                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `NormalizedFormula` is the internal object-language syntax
│          used for effective checking. Variables retain natural
│          indices, while implication stores its children directly
│          instead of nesting arithmetic pair codes.
│
*)

Inductive NormalizedFormula : Type :=
| NFVar : nat -> NormalizedFormula
| NFImp : NormalizedFormula -> NormalizedFormula -> NormalizedFormula.

(*
│
│          `NormalizedRule` is the typed rule vocabulary. K and S need
│          no payload; MP stores the two cited prefix indices
│          directly.
│
*)

Inductive NormalizedRule : Type :=
| NRAxK : NormalizedRule
| NRAxS : NormalizedRule
| NRMP : nat -> nat -> NormalizedRule.

(*
│
│          A normalized line pairs a typed rule with the typed formula
│          displayed at that derivation position. No canonicity guard
│          is needed because malformed arithmetic shapes are
│          unrepresentable.
│
*)

Record NormalizedLine : Type :=
  Build_NormalizedLine {
    normalized_line_rule : NormalizedRule;
    normalized_line_formula : NormalizedFormula
  }.

(*
│
│          A normalized derivation is an ordinary finite list of
│          normalized lines, processed from left to right.
│
*)

Definition NormalizedDerivation : Type := list NormalizedLine.

(*
│
│          `normalized_formula_eqb` is structural equality for
│          normalized formulas: variable indices use `Nat.eqb`, and
│          implications compare both children recursively.
│
*)

(*                  normalized_formula_eqb(A,B)=true ⇔ A=B.                   *)

Fixpoint normalized_formula_eqb
  (a b : NormalizedFormula)
  : bool :=
  match a, b with
  | NFVar i, NFVar j => Nat.eqb i j
  | NFImp a1 a2, NFImp b1 b2 =>
      normalized_formula_eqb a1 b1 && normalized_formula_eqb a2 b2
  | _, _ => false
  end.

(*
│
│          The formula equality checker reflects exactly to
│          propositional equality, providing the bridge used in every
│          normalized rule proof.
│
*)

Lemma normalized_formula_eqb_eq :
  forall a b,
    normalized_formula_eqb a b = true <-> a = b.
Proof.
  induction a as [i|a1 IHa1 a2 IHa2];
    destruct b as [j|b1 b2]; simpl.
  - rewrite Nat.eqb_eq.
    split.
    + intro H. subst. reflexivity.
    + intro H. inversion H. reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff, IHa1, IHa2.
    split.
    + intros [H1 H2]. subst. reflexivity.
    + intro H. inversion H. auto.
Qed.

(*
│
│          Structural formula equality is reflexive; this forward form
│          is convenient when proving checker completeness.
│
*)

Lemma normalized_formula_eqb_refl :
  forall a, normalized_formula_eqb a a = true.
Proof.
  intro a.
  apply normalized_formula_eqb_eq.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           NORMALIZED LOCAL CHECKER                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `normalized_stepb prefix rule formula` checks one typed
│          derivation step against formulas already accepted in
│          `prefix`. K and S are recognized by direct pattern
│          matching; MP retrieves its two cited prefix formulas and
│          compares antecedent and consequent structurally.
│
*)

(*                normalized_stepb(prefix,NRAxK,A→(B→A))=true.                *)
(*        normalized_stepb(prefix,NRAxS,(A→(B→C))→((A→B)→(A→C)))=true.        *)
(* prefix[p]=A ∧ prefix[q]=(A→B) ⇒ normalized_stepb(prefix,NRMP(p,q),B)=true. *)

Definition normalized_stepb
  (prefix : list NormalizedFormula)
  (rule : NormalizedRule)
  (formula : NormalizedFormula)
  : bool :=
  match rule with
  | NRAxK =>
      match formula with
      | NFImp A (NFImp _ A') => normalized_formula_eqb A A'
      | _ => false
      end
  | NRAxS =>
      match formula with
      | NFImp
          (NFImp A (NFImp B C))
          (NFImp (NFImp A1 B1) (NFImp A2 C1)) =>
          normalized_formula_eqb A A1
          && normalized_formula_eqb A A2
          && normalized_formula_eqb B B1
          && normalized_formula_eqb C C1
      | _ => false
      end
  | NRMP p q =>
      match nth_error prefix p, nth_error prefix q with
      | Some A, Some (NFImp A' B) =>
          normalized_formula_eqb A A'
          && normalized_formula_eqb formula B
      | _, _ => false
      end
  end.

(*
│
│          `NormalizedStep` is the independent propositional rule
│          judgment mirrored by `normalized_stepb`. Its constructors
│          state K, S, and MP directly over inductive formulas and
│          explicit prefix lookup equations.
│
*)

Inductive NormalizedStep
  (prefix : list NormalizedFormula)
  : NormalizedRule -> NormalizedFormula -> Prop :=
| NormalizedStep_K : forall A B,
    NormalizedStep prefix NRAxK (NFImp A (NFImp B A))
| NormalizedStep_S : forall A B C,
    NormalizedStep prefix NRAxS
      (NFImp
        (NFImp A (NFImp B C))
        (NFImp (NFImp A B) (NFImp A C)))
| NormalizedStep_MP : forall p q A B,
    nth_error prefix p = Some A ->
    nth_error prefix q = Some (NFImp A B) ->
    NormalizedStep prefix (NRMP p q) B.

(*
│
│          Local checker soundness inverts every successful Boolean
│          branch into the corresponding inductive rule constructor,
│          recovering formula equalities and MP lookup evidence.
│
*)

(*   normalized_stepb(prefix,rule,φ)=true ⇒ NormalizedStep(prefix,rule,φ).    *)

Theorem normalized_stepb_sound :
  forall prefix rule formula,
    normalized_stepb prefix rule formula = true ->
    NormalizedStep prefix rule formula.
Proof.
  intros prefix rule formula Hcheck.
  destruct rule as [| |p q].
  - destruct formula as [i|A rhs]; try discriminate.
    destruct rhs as [j|B A']; try discriminate.
    simpl in Hcheck.
    apply normalized_formula_eqb_eq in Hcheck.
    subst A'. constructor.
  - destruct formula as [i|lhs rhs]; try discriminate.
    destruct lhs as [i|A BC]; try discriminate.
    destruct BC as [i|B C]; try discriminate.
    destruct rhs as [i|AB AC]; try discriminate.
    destruct AB as [i|A1 B1]; try discriminate.
    destruct AC as [i|A2 C1]; try discriminate.
    simpl in Hcheck.
    repeat rewrite Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [[[HA1 HA2] HB] HC].
    apply normalized_formula_eqb_eq in HA1.
    apply normalized_formula_eqb_eq in HA2.
    apply normalized_formula_eqb_eq in HB.
    apply normalized_formula_eqb_eq in HC.
    subst A1 A2 B1 C1. constructor.
  - simpl in Hcheck.
    destruct (nth_error prefix p) as [A|] eqn:Hp; try discriminate.
    destruct (nth_error prefix q) as [qf|] eqn:Hq; try discriminate.
    destruct qf as [i|A' B]; try discriminate.
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [HA HB].
    apply normalized_formula_eqb_eq in HA.
    apply normalized_formula_eqb_eq in HB.
    subst A' formula.
    econstructor; eauto.
Qed.

(*
│
│          Local checker completeness evaluates every inductively
│          valid K, S, or MP step to Boolean acceptance.
│
*)

(*   NormalizedStep(prefix,rule,φ) ⇒ normalized_stepb(prefix,rule,φ)=true.    *)

Theorem normalized_stepb_complete :
  forall prefix rule formula,
    NormalizedStep prefix rule formula ->
    normalized_stepb prefix rule formula = true.
Proof.
  intros prefix rule formula Hstep.
  inversion Hstep; subst; simpl.
  - apply normalized_formula_eqb_refl.
  - repeat rewrite normalized_formula_eqb_refl. reflexivity.
  - rewrite H, H0.
    repeat rewrite normalized_formula_eqb_refl.
    reflexivity.
Qed.

(*
│
│          `normalized_stepb_iff` packages soundness and completeness
│          as the local reflection theorem: executable acceptance and
│          inductive rule validity coincide.
│
*)

(*   normalized_stepb(prefix,rule,φ)=true ⇔ NormalizedStep(prefix,rule,φ).    *)

Theorem normalized_stepb_iff :
  forall prefix rule formula,
    normalized_stepb prefix rule formula = true <->
    NormalizedStep prefix rule formula.
Proof.
  split.
  - apply normalized_stepb_sound.
  - apply normalized_stepb_complete.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            NORMALIZED DERIVATIONS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `normalized_linesb prefix lines` checks a derivation tail
│          from left to right. After each accepted line, its displayed
│          formula is appended to the prefix available to later MP
│          citations.
│
*)

(*                     normalized_linesb(prefix,[])=true.                     *)
(*                    normalized_linesb(prefix,line::rest)                    *)
(*            = normalized_stepb(prefix,rule(line),formula(line))             *)
(*             ∧? normalized_linesb(prefix⋅[formula(line)],rest).             *)

Fixpoint normalized_linesb
  (prefix : list NormalizedFormula)
  (lines : NormalizedDerivation)
  : bool :=
  match lines with
  | [] => true
  | line :: rest =>
      normalized_stepb
        prefix
        (normalized_line_rule line)
        (normalized_line_formula line)
      && normalized_linesb
          (prefix ++ [normalized_line_formula line])
          rest
  end.

(*
│
│          `NormalizedLines prefix lines` is the inductive
│          whole-derivation judgment. Its cons constructor requires
│          one valid local step and recursively validates the
│          remainder under the prefix extended by that line's formula.
│
*)

Inductive NormalizedLines :
  list NormalizedFormula -> NormalizedDerivation -> Prop :=
| NormalizedLines_nil : forall prefix,
    NormalizedLines prefix []
| NormalizedLines_cons : forall prefix rule formula rest,
    NormalizedStep prefix rule formula ->
    NormalizedLines (prefix ++ [formula]) rest ->
    NormalizedLines prefix
      (Build_NormalizedLine rule formula :: rest).

(*
│
│          Whole-derivation soundness lifts local reflection through
│          the line list: every successful normalized computation
│          yields an inductive derivation witness.
│
*)

(*   normalized_linesb(prefix,lines)=true ⇒ NormalizedLines(prefix,lines).    *)

Theorem normalized_linesb_sound :
  forall prefix lines,
    normalized_linesb prefix lines = true ->
    NormalizedLines prefix lines.
Proof.
  intros prefix lines.
  revert prefix.
  induction lines as [|line rest IH]; intros prefix Hcheck.
  - constructor.
  - destruct line as [rule formula].
    simpl in Hcheck.
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hstep Hrest].
    constructor.
    + apply normalized_stepb_sound. exact Hstep.
    + apply IH. exact Hrest.
Qed.

(*
│
│          Whole-derivation completeness evaluates every inductively
│          valid normalized line sequence to Boolean acceptance.
│
*)

(*   NormalizedLines(prefix,lines) ⇒ normalized_linesb(prefix,lines)=true.    *)

Theorem normalized_linesb_complete :
  forall prefix lines,
    NormalizedLines prefix lines ->
    normalized_linesb prefix lines = true.
Proof.
  intros prefix lines Hlines.
  induction Hlines.
  - reflexivity.
  - simpl.
    apply Bool.andb_true_iff.
    split.
    + apply normalized_stepb_complete. exact H.
    + exact IHHlines.
Qed.

(*
│
│          `normalized_linesb_iff` is the package's principal
│          normalization theorem: the effective structural checker
│          accepts exactly the inductively valid derivations.
│
*)

(*   normalized_linesb(prefix,lines)=true ⇔ NormalizedLines(prefix,lines).    *)

Theorem normalized_linesb_iff :
  forall prefix lines,
    normalized_linesb prefix lines = true <->
    NormalizedLines prefix lines.
Proof.
  split.
  - apply normalized_linesb_sound.
  - apply normalized_linesb_complete.
Qed.
