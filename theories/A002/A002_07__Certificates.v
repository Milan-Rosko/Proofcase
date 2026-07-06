(*A002_07__Certificates.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / A002_07__Certificates                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Certificate layer for A002-Core. We give stable names to the local and
  final certificate encodings produced by the verifier core, provide
  arithmetic projections for those payloads, and implement the executable
  certificate checker.

  The initial checker is deliberately conservative: `A002_Certb d theta p`
  reruns the arithmetic verifier and accepts exactly when `p` is the
  verifier-generated certificate payload for `(d, theta)`. Thus the checker
  is total, deterministic, arithmetic, and immediately agrees with generated
  certificates. A later layer may replace this equality check with a
  decompositional replay checker over the certificate fields.

*)

From A002 Require Export A002_06__Verifier_Core.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              LOCAL CERTIFICATES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A local certificate records the line index together with
│          the successful local rule-checker payload.
│
*)

Definition code_local_cert (j rule payload : nat) : nat :=
  encode j (encode rule payload).

(*
│
│          The verifier core stores the already packaged local rule
│          payload, so this bridge names the exact payload format used
│          by `verify_line`.
│
*)

Definition code_local_cert_from_checked (j checked_rule : nat) : nat :=
  code_local_cert_payload j checked_rule.

(*
│
│          `local_cert_index` projects the line index from a local
│          certificate.
│
*)

Definition local_cert_index (cert : nat) : nat :=
  fst001 cert.

(*
│
│          `local_cert_rule_payload` projects the packed rule/payload
│          component from a local certificate.
│
*)

Definition local_cert_rule_payload (cert : nat) : nat :=
  snd001 cert.

(*
│
│          `local_cert_rule` projects the rule code from a local
│          certificate.
│
*)

Definition local_cert_rule (cert : nat) : nat :=
  fst001 (local_cert_rule_payload cert).

(*
│
│          `local_cert_payload` projects the rule-specific payload
│          from a local certificate.
│
*)

Definition local_cert_payload (cert : nat) : nat :=
  snd001 (local_cert_rule_payload cert).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             GLOBAL CERTIFICATES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The final certificate records the derivation length,
│          target, local certificate list, and final displayed
│          formula.
│
*)

Definition code_global_cert
  (n theta certs final_formula : nat)
  : nat :=
  code_final_cert_payload n theta certs final_formula.

(*
│
│          `cert_length` projects the claimed derivation length from a
│          final certificate payload.
│
*)

Definition cert_length (p : nat) : nat :=
  fst001 p.

(*
│
│          `cert_tail` projects the packed
│          target/certificates/final-formula tail from a final
│          certificate payload.
│
*)

Definition cert_tail (p : nat) : nat :=
  snd001 p.

(*
│
│          `cert_target` projects the target code recorded in a final
│          certificate payload.
│
*)

Definition cert_target (p : nat) : nat :=
  fst001 (cert_tail p).

(*
│
│          `cert_body` projects the packed
│          local-certificate-list/final-formula component.
│
*)

Definition cert_body (p : nat) : nat :=
  snd001 (cert_tail p).

(*
│
│          `cert_local_list` projects the tagged list of local
│          certificates. The verifier core accumulates this list in
│          reverse verification order.
│
*)

Definition cert_local_list (p : nat) : nat :=
  fst001 (cert_body p).

(*
│
│          `cert_final_formula` projects the final displayed formula
│          recorded by the verifier.
│
*)

Definition cert_final_formula (p : nat) : nat :=
  snd001 (cert_body p).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             CERTIFICATE CHECKER                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `A002_Certb d theta p` is the executable certificate
│          checker. It accepts exactly the certificate payload
│          generated by `A002_Verify d theta`.
│
*)

Definition A002_Certb (d theta p : nat) : bool :=
  Nat.eqb (A002_Verify d theta) (accept p).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CERTIFICATE FACTS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A verifier-generated certificate is accepted by the
│          certificate checker.
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
│          The global certificate constructor exposes its recorded
│          derivation length.
│
*)

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
│          target.
│
*)

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
│          The global certificate constructor exposes its local
│          certificate list.
│
*)

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
│          displayed formula.
│
*)

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
