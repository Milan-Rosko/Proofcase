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

  Normalization and verification layer for CARRYLESS SEQUENT. We retain the
  arithmetic verifier surface, package its certificates and basic theorems,
  and provide an inductive normal form on which effectivity can be checked
  without materializing nested A001 codes.

  The first half of this file preserves the original A001-coded verifier as
  an extraction and compatibility surface. The second half is the certified
  effectivity boundary: arithmetic formulas and derivations normalize to
  inductive data, structural checking is reflected into independent K/S/MP
  judgments, target-sensitive verification rejects empty or wrong-conclusion
  proofs, and the public arithmetic entry point is gated by that normalized
  proof check.

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

(*
│
│          The loop invariant is operational: indices below `j` have
│          already been checked, and `certs` contains their local
│          certificates in reverse order. If `j = n`, the accumulator
│          is accepted immediately; otherwise one successful line
│          extends the accumulator and advances both the index and the
│          structural recursion.
│
*)

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

(*
│
│          Verification proceeds in a fixed order: canonical header,
│          exact tagged-list length, non-emptiness, local line loop,
│          final-line retrieval, and target equality. This ordering
│          makes rejection deterministic and assigns every failure to
│          the earliest applicable stage.
│
*)

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

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                   TARGET-SENSITIVE NORMALIZED VERIFICATION                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `normalized_conclusion` returns the formula displayed by
│          the final line of a nonempty normalized derivation.
│
*)

Fixpoint normalized_conclusion
  (lines : NormalizedDerivation)
  : option NormalizedFormula :=
  match lines with
  | [] => None
  | line :: rest =>
      match rest with
      | [] => Some (normalized_line_formula line)
      | _ => normalized_conclusion rest
      end
  end.

(*
│
│          `normalized_verifyb lines target` requires a rule-correct
│          line sequence and equality between its final displayed
│          formula and the requested target. Empty derivations are
│          rejected because they have no conclusion.
│
*)

Definition normalized_verifyb
  (lines : NormalizedDerivation)
  (target : NormalizedFormula)
  : bool :=
  normalized_linesb [] lines
  && match normalized_conclusion lines with
     | Some conclusion => normalized_formula_eqb conclusion target
     | None => false
     end.

(*
│
│          `NormalizedProof lines target` is the independent
│          target-sensitive validity proposition: all lines are
│          inductively valid and the last line displays `target`.
│
*)

Definition NormalizedProof
  (lines : NormalizedDerivation)
  (target : NormalizedFormula)
  : Prop :=
  NormalizedLines [] lines /\
  normalized_conclusion lines = Some target.

(*   normalized_verifyb(lines,target)=true ⇔ NormalizedProof(lines,target).   *)

Theorem normalized_verifyb_iff :
  forall lines target,
    normalized_verifyb lines target = true <->
    NormalizedProof lines target.
Proof.
  intros lines target.
  unfold normalized_verifyb, NormalizedProof.
  rewrite Bool.andb_true_iff.
  rewrite normalized_linesb_iff.
  destruct (normalized_conclusion lines) as [conclusion|] eqn:Hconclusion.
  - rewrite normalized_formula_eqb_eq.
    split.
    + intros [Hlines Heq].
      subst conclusion.
      split.
      * exact Hlines.
      * reflexivity.
    + intros [Hlines Htarget].
      inversion Htarget.
      split.
      * exact Hlines.
      * reflexivity.
  - split.
    + intros [_ Hfalse]. discriminate.
    + intros [_ Hfalse]. discriminate.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           ARITHMETIC NORMALIZATION                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Fixpoint normalized_formula_height
  (formula : NormalizedFormula)
  : nat :=
  match formula with
  | NFVar _ => 0
  | NFImp A B => S (Nat.max (normalized_formula_height A)
                            (normalized_formula_height B))
  end.

Fixpoint encode_normalized_formula_raw
  (formula : NormalizedFormula)
  : nat :=
  match formula with
  | NFVar i => code_var i
  | NFImp A B =>
      code_imp (encode_normalized_formula_raw A)
               (encode_normalized_formula_raw B)
  end.

(*
│
│          Certified formula quotation stores an explicit positive
│          structural fuel bound beside the raw arithmetic syntax
│          tree. This makes normalization complete without deriving
│          recursion depth from the rapidly growing raw code.
│
*)

Definition encode_normalized_formula
  (formula : NormalizedFormula)
  : nat :=
  encode (S (normalized_formula_height formula))
         (encode_normalized_formula_raw formula).

(*
│
│          `normalize_formula_fuel` converts a canonical arithmetic
│          formula tree into the inductive normal form. The explicit
│          fuel is consumed only when descending through implication
│          nodes.
│
*)

Fixpoint normalize_formula_fuel
  (fuel c : nat)
  : option NormalizedFormula :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if canonical001b c then
        let tag := formula_tag c in
        let payload := formula_payload c in
        if Nat.eqb tag TAG_VAR then
          Some (NFVar payload)
        else if Nat.eqb tag TAG_IMP then
          if canonical001b payload then
            match normalize_formula_fuel fuel' (fst001 payload),
                  normalize_formula_fuel fuel' (snd001 payload) with
            | Some A, Some B => Some (NFImp A B)
            | _, _ => None
            end
          else None
        else None
      else None
  end.

Definition normalize_formula (c : nat) : option NormalizedFormula :=
  if canonical001b c then
    normalize_formula_fuel (fst001 c) (snd001 c)
  else None.

Lemma normalize_formula_fuel_encode_raw :
  forall fuel formula,
    normalized_formula_height formula < fuel ->
    normalize_formula_fuel fuel (encode_normalized_formula_raw formula) =
    Some formula.
Proof.
  intros fuel formula.
  revert fuel.
  induction formula as [i|A IHA B IHB]; intros fuel Hfuel.
  - destruct fuel as [|fuel']; [lia|].
    cbn [normalized_formula_height] in Hfuel.
    cbn [normalized_formula_height encode_normalized_formula_raw
      normalize_formula_fuel].
    unfold code_var, formula_tag, formula_payload.
    rewrite canonical001b_encode.
    rewrite fst001_encode.
    rewrite snd001_encode.
    rewrite Nat.eqb_refl.
    reflexivity.
  - destruct fuel as [|fuel']; [lia|].
    cbn [normalized_formula_height] in Hfuel.
    cbn [normalized_formula_height encode_normalized_formula_raw
      normalize_formula_fuel].
    unfold code_imp, formula_tag, formula_payload.
    rewrite canonical001b_encode.
    rewrite fst001_encode.
    rewrite snd001_encode.
    cbn [TAG_VAR TAG_IMP].
    rewrite Nat.eqb_refl.
    rewrite canonical001b_encode.
    rewrite fst001_encode.
    rewrite snd001_encode.
    rewrite IHA.
    2: {
      pose proof
        (Nat.le_max_l (normalized_formula_height A)
                      (normalized_formula_height B)).
      lia.
    }
    rewrite IHB.
    2: {
      pose proof
        (Nat.le_max_r (normalized_formula_height A)
                      (normalized_formula_height B)).
      lia.
    }
    reflexivity.
Qed.

Theorem normalize_encode_normalized_formula :
  forall formula,
    normalize_formula (encode_normalized_formula formula) = Some formula.
Proof.
  intro formula.
  unfold normalize_formula, encode_normalized_formula.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  apply normalize_formula_fuel_encode_raw.
  lia.
Qed.

(*
│
│          `normalize_rule` converts a canonical arithmetic K, S, or
│          MP tag into its typed rule constructor.
│
*)

Definition normalize_rule (tag : nat) : option NormalizedRule :=
  if canonical001b tag then
    let rule := rule_code tag in
    let payload := rule_payload tag in
    if Nat.eqb rule RULE_AXK then
      if Nat.eqb payload 0 then Some NRAxK else None
    else if Nat.eqb rule RULE_AXS then
      if Nat.eqb payload 0 then Some NRAxS else None
    else if Nat.eqb rule RULE_MP then
      if canonical001b payload then
        Some (NRMP (fst001 payload) (snd001 payload))
      else None
    else None
  else None.

Definition encode_normalized_rule (rule : NormalizedRule) : nat :=
  match rule with
  | NRAxK => tag_axk
  | NRAxS => tag_axs
  | NRMP p q => tag_mp p q
  end.

Theorem normalize_encode_normalized_rule :
  forall rule,
    normalize_rule (encode_normalized_rule rule) = Some rule.
Proof.
  intro rule.
  destruct rule as [| |p q].
  - unfold encode_normalized_rule, normalize_rule, tag_axk,
      rule_code, rule_payload.
    rewrite canonical001b_encode, fst001_encode, snd001_encode.
    reflexivity.
  - unfold encode_normalized_rule, normalize_rule, tag_axs,
      rule_code, rule_payload.
    rewrite canonical001b_encode, fst001_encode, snd001_encode.
    reflexivity.
  - unfold encode_normalized_rule, normalize_rule, tag_mp,
      rule_code, rule_payload.
    rewrite canonical001b_encode, fst001_encode, snd001_encode.
    rewrite canonical001b_encode, fst001_encode, snd001_encode.
    reflexivity.
Qed.

(*
│
│          `normalize_line` requires a canonical arithmetic line, a
│          recognized rule tag, and a recursively normalized displayed
│          formula.
│
*)

Definition normalize_line (ell : nat) : option NormalizedLine :=
  if canonical001b ell then
    match normalize_rule (line_tag ell),
          normalize_formula (line_formula ell) with
    | Some rule, Some formula =>
        Some (Build_NormalizedLine rule formula)
    | _, _ => None
    end
  else None.

Definition encode_normalized_line (line : NormalizedLine) : nat :=
  code_line
    (encode_normalized_rule (normalized_line_rule line))
    (encode_normalized_formula (normalized_line_formula line)).

Theorem normalize_encode_normalized_line :
  forall line,
    normalize_line (encode_normalized_line line) = Some line.
Proof.
  intros [rule formula].
  unfold encode_normalized_line, normalize_line, code_line,
    line_tag, line_formula.
  rewrite canonical001b_encode, fst001_encode, snd001_encode.
  rewrite normalize_encode_normalized_rule.
  rewrite normalize_encode_normalized_formula.
  reflexivity.
Qed.

(*
│
│          `normalize_lines n body` consumes exactly `n` canonical
│          cons cells and requires the unique nil node at the end,
│          converting every arithmetic line along the way.
│
*)

Fixpoint normalize_lines
  (n body : nat)
  : option NormalizedDerivation :=
  match n with
  | 0 =>
      if is_nil_nodeb body then Some [] else None
  | S n' =>
      if canonical001b body then
        if Nat.eqb (list_tag body) TAG_CONS then
          let payload := list_payload body in
          if canonical001b payload then
            match normalize_line (fst001 payload),
                  normalize_lines n' (snd001 payload) with
            | Some line, Some rest => Some (line :: rest)
            | _, _ => None
            end
          else None
        else None
      else None
  end.

Fixpoint encode_normalized_lines
  (lines : NormalizedDerivation)
  : nat :=
  match lines with
  | [] => code_nil
  | line :: rest =>
      code_cons (encode_normalized_line line)
                (encode_normalized_lines rest)
  end.

Theorem normalize_encode_normalized_lines :
  forall lines,
    normalize_lines (length lines) (encode_normalized_lines lines) =
    Some lines.
Proof.
  intro lines.
  induction lines as [|line rest IH].
  - change
      ((if is_nil_nodeb code_nil
        then Some (@nil NormalizedLine)
        else None) = Some (@nil NormalizedLine)).
    rewrite is_nil_nodeb_code_nil.
    reflexivity.
  - cbn [length normalize_lines encode_normalized_lines].
    unfold code_cons, list_tag, list_payload.
    rewrite canonical001b_encode, fst001_encode, snd001_encode.
    rewrite Nat.eqb_refl.
    rewrite canonical001b_encode, fst001_encode, snd001_encode.
    rewrite normalize_encode_normalized_line.
    rewrite IH.
    reflexivity.
Qed.

(*
│
│          `normalize_derivation` converts a canonical arithmetic
│          header and its exact tagged line body into a normalized
│          derivation.
│
*)

Definition normalize_derivation
  (d : nat)
  : option NormalizedDerivation :=
  if canonical001b d then
    normalize_lines (fst001 d) (snd001 d)
  else None.

Definition encode_normalized_derivation
  (lines : NormalizedDerivation)
  : nat :=
  code_derivation (length lines) (encode_normalized_lines lines).

Theorem normalize_encode_normalized_derivation :
  forall lines,
    normalize_derivation (encode_normalized_derivation lines) = Some lines.
Proof.
  intro lines.
  unfold normalize_derivation, encode_normalized_derivation,
    code_derivation.
  rewrite canonical001b_encode, fst001_encode, snd001_encode.
  apply normalize_encode_normalized_lines.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       CERTIFIED ARITHMETIC ENTRY POINT                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `normalized_failure_index prefix lines index` replays
│          normalized lines from the supplied global offset and
│          returns the zero-based index of the first failed K, S, or
│          MP obligation. `None` means that every line passed.
│
*)

Fixpoint normalized_failure_index
  (prefix : list NormalizedFormula)
  (lines : NormalizedDerivation)
  (index : nat)
  : option nat :=
  match lines with
  | [] => None
  | line :: rest =>
      if normalized_stepb
           prefix
           (normalized_line_rule line)
           (normalized_line_formula line) then
        normalized_failure_index
          (prefix ++ [normalized_line_formula line])
          rest
          (S index)
      else Some index
  end.

(*
│
│          Failure-index reflection proves that absence of a reported
│          line is equivalent to acceptance by the complete normalized
│          line checker. Thus the diagnostic traversal and the
│          proof-checking traversal agree on whether a rule failure
│          exists.
│
*)

Theorem normalized_failure_index_none_iff :
  forall prefix lines index,
    normalized_failure_index prefix lines index = None <->
    normalized_linesb prefix lines = true.
Proof.
  intros prefix lines.
  revert prefix.
  induction lines as [|[rule formula] rest IH]; intros prefix index.
  - cbn [normalized_failure_index normalized_linesb].
    split; reflexivity.
  - change
      ((if normalized_stepb prefix rule formula then
          normalized_failure_index
            (prefix ++ [formula]) rest (S index)
        else Some index) = None <->
       normalized_stepb prefix rule formula &&
         normalized_linesb (prefix ++ [formula]) rest = true).
    destruct (normalized_stepb prefix rule formula) eqn:Hstep.
    + apply IH.
    + split; discriminate.
Qed.

(*
│
│          `normalized_rejection` classifies a failed target-sensitive
│          normalized check. A first failed rule is reported at its
│          line index; otherwise an absent conclusion is an empty
│          derivation and a present conclusion is a target mismatch at
│          the last line.
│
*)

Definition normalized_rejection
  (lines : NormalizedDerivation)
  : nat :=
  match normalized_failure_index [] lines 0 with
  | Some index =>
      reject STAGE_RULE index ERR_NORMALIZED_STEP_REJECTED
  | None =>
      match normalized_conclusion lines with
      | None =>
          reject STAGE_CONCLUSION 0 ERR_EMPTY_DERIVATION
      | Some _ =>
          reject STAGE_CONCLUSION
            (Nat.pred (length lines))
            ERR_BAD_CONCLUSION
      end
  end.

Lemma reject_not_accept :
  forall stage index detail payload,
    reject stage index detail <> accept payload.
Proof.
  intros stage index detail payload Heq.
  apply (f_equal fst001) in Heq.
  unfold reject, accept in Heq.
  repeat rewrite fst001_encode in Heq.
  discriminate.
Qed.

Lemma normalized_rejection_not_accept :
  forall lines payload,
    normalized_rejection lines <> accept payload.
Proof.
  intros lines payload.
  unfold normalized_rejection.
  destruct (normalized_failure_index [] lines 0) as [index|].
  - apply reject_not_accept.
  - destruct (normalized_conclusion lines).
    + apply reject_not_accept.
    + apply reject_not_accept.
Qed.

Definition certified_payload (d theta : nat) : nat :=
  encode d theta.

(*
│
│          `A002_Verify_certified` normalizes the arithmetic
│          derivation and target, requires target-sensitive normalized
│          validity, and returns a canonical payload binding the
│          accepted derivation code to its target code. Rejection
│          distinguishes derivation normalization, target
│          normalization, first normalized rule failure, emptiness,
│          and conclusion mismatch.
│
*)

Definition A002_Verify_certified
  (d theta : nat)
  : nat :=
  match normalize_derivation d, normalize_formula theta with
  | Some lines, Some target =>
      if normalized_verifyb lines target then
        accept (certified_payload d theta)
      else
        normalized_rejection lines
  | None, _ =>
      reject STAGE_DERIVATION_HEADER 0 ERR_NONCANONICAL_DERIVATION
  | Some _, None =>
      reject STAGE_FORMULA 0 ERR_NONCANONICAL_FORMULA
  end.

Definition A002_Certified_Certb
  (d theta payload : nat)
  : bool :=
  canonical001b payload
  && Nat.eqb (fst001 payload) d
  && Nat.eqb (snd001 payload) theta
  && match normalize_derivation d, normalize_formula theta with
     | Some lines, Some target => normalized_verifyb lines target
     | _, _ => false
     end.

(*
│
│          Independent certificate replay equivalence: a certified
│          payload checks exactly when it canonically binds the
│          supplied derivation and target codes and those codes
│          normalize to a target-sensitive inductive proof. The
│          checker does not call either arithmetic verifier.
│
*)

Theorem certified_certb_iff :
  forall d theta payload,
    A002_Certified_Certb d theta payload = true <->
    payload = certified_payload d theta /\
    exists lines target,
      normalize_derivation d = Some lines /\
      normalize_formula theta = Some target /\
      NormalizedProof lines target.
Proof.
  intros d theta payload.
  unfold A002_Certified_Certb.
  repeat rewrite Bool.andb_true_iff.
  split.
  - intros [[[Hcanonical Hfst] Hsnd] Hreplay].
    apply Nat.eqb_eq in Hfst.
    apply Nat.eqb_eq in Hsnd.
    assert (Hpayload : payload = certified_payload d theta).
    {
      apply canonical001b_eq in Hcanonical.
      unfold recode001, certified_payload in Hcanonical.
      rewrite Hfst, Hsnd in Hcanonical.
      symmetry.
      exact Hcanonical.
    }
    split.
    + exact Hpayload.
    + destruct (normalize_derivation d) as [lines|] eqn:Hlines;
        try discriminate.
      destruct (normalize_formula theta) as [target|] eqn:Htarget;
        try discriminate.
      exists lines, target.
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- apply normalized_verifyb_iff.
           exact Hreplay.
  - intros [Hpayload [lines [target [Hlines [Htarget Hproof]]]]].
    subst payload.
    unfold certified_payload.
    rewrite canonical001b_encode.
    rewrite fst001_encode, snd001_encode.
    repeat rewrite Nat.eqb_refl.
    rewrite Hlines, Htarget.
    repeat split; try reflexivity.
    apply (proj2 (normalized_verifyb_iff lines target)).
    exact Hproof.
Qed.

(*
│
│          End-to-end arithmetic soundness: any accepted arithmetic
│          result has a successfully normalized derivation and target
│          satisfying the independent inductive proof judgment.
│
*)

Theorem certified_verify_accept_sound :
  forall d theta payload,
    A002_Verify_certified d theta = accept payload ->
    exists lines target,
      normalize_derivation d = Some lines /\
      normalize_formula theta = Some target /\
      NormalizedProof lines target.
Proof.
  intros d theta payload Haccept.
  unfold A002_Verify_certified in Haccept.
  destruct (normalize_derivation d) as [lines|] eqn:Hlines.
  - destruct (normalize_formula theta) as [target|] eqn:Htarget.
    + destruct (normalized_verifyb lines target) eqn:Hverify.
      * exists lines, target.
        split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ apply normalized_verifyb_iff.
              exact Hverify.
      * exfalso.
        eapply normalized_rejection_not_accept.
        exact Haccept.
    + exfalso.
      eapply reject_not_accept.
      exact Haccept.
  - exfalso.
    eapply reject_not_accept.
    exact Haccept.
Qed.

Theorem certified_verify_accept_payload :
  forall d theta payload,
    A002_Verify_certified d theta = accept payload ->
    payload = certified_payload d theta.
Proof.
  intros d theta payload Haccept.
  unfold A002_Verify_certified in Haccept.
  destruct (normalize_derivation d) as [lines|] eqn:Hlines.
  - destruct (normalize_formula theta) as [target|] eqn:Htarget.
    + destruct (normalized_verifyb lines target) eqn:Hverify.
      * apply (f_equal snd001) in Haccept.
        unfold accept in Haccept.
        repeat rewrite snd001_encode in Haccept.
        symmetry.
        exact Haccept.
      * exfalso.
        eapply normalized_rejection_not_accept.
        exact Haccept.
    + exfalso.
      eapply reject_not_accept.
      exact Haccept.
  - exfalso.
    eapply reject_not_accept.
    exact Haccept.
Qed.

(*
│
│          Completeness of the certified arithmetic quotation: every
│          inductively valid target-sensitive proof has a canonical
│          arithmetic derivation and target encoding accepted by
│          `A002_Verify_certified`.
│
*)

Theorem certified_verify_complete :
  forall lines target,
    NormalizedProof lines target ->
    A002_Verify_certified
      (encode_normalized_derivation lines)
      (encode_normalized_formula target) =
    accept
      (certified_payload
        (encode_normalized_derivation lines)
        (encode_normalized_formula target)).
Proof.
  intros lines target Hproof.
  unfold A002_Verify_certified.
  rewrite normalize_encode_normalized_derivation.
  rewrite normalize_encode_normalized_formula.
  apply normalized_verifyb_iff in Hproof.
  rewrite Hproof.
  reflexivity.
Qed.

Theorem certified_generated_cert_checks :
  forall d theta payload,
    A002_Verify_certified d theta = accept payload ->
    A002_Certified_Certb d theta payload = true.
Proof.
  intros d theta payload Haccept.
  apply certified_certb_iff.
  split.
  - apply certified_verify_accept_payload.
    exact Haccept.
  - exact (certified_verify_accept_sound d theta payload Haccept).
Qed.
