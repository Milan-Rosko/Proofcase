(*A002_08__Soundness.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / A002_08__Soundness                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Soundness layer for A002-Core. We connect verifier acceptance to the
  executable certificate checker, record generated-certificate agreement, and
  expose deterministic functional behavior of the arithmetic verifier.

  This first soundness layer is intentionally tied to the executable artifact
  surface already built in files 00--07. The local checker facts below
  certify the status/payload shape of accepted arithmetic checker results;
  later strengthening can add full parser-inversion statements for the K, S,
  and MP syntactic schemas.

*)

From A002 Require Export A002_07__Certificates.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                     ACCEPTANCE AND CERTIFICATE AGREEMENT                     │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          If the verifier accepts with payload `p`, then the
│          executable certificate checker accepts `p` for the same
│          derivation and target.
│
*)

Theorem A002_Verify_accept_sound :
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
│          Generated certificate agreement is the same executable fact
│          stated under the artifact-facing theorem name.
│
*)

Theorem A002_generated_cert_checks :
  forall d theta p,
    A002_Verify d theta = encode 1 p ->
    A002_Certb d theta p = true.
Proof.
  intros d theta p Hverify.
  apply A002_Verify_accept_sound.
  exact Hverify.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 DETERMINISM                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The verifier is deterministic because it is an ordinary
│          total function on natural numbers.
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
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        LOCAL CHECKER ACCEPTANCE SHAPE                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Accepted K-checker results have acceptance status and
│          expose the reported certificate payload.
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
│          Accepted S-checker results have acceptance status and
│          expose the reported certificate payload.
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
│          Accepted MP-checker results have acceptance status and
│          expose the reported certificate payload.
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
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                  FUEL GUARD                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          When the line loop is already positioned at the end of the
│          derivation, one positive fuel step is enough to accept the
│          accumulated certificates.
│
*)

Lemma verify_lines_no_fuel_failure_at_end :
  forall fuel n body certs,
    verify_lines (S fuel) n body n certs = accept certs.
Proof.
  apply verify_lines_at_end.
Qed.
