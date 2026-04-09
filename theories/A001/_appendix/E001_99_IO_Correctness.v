(*E001_99_IO_Correctness.v*)
(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│            _____            EFFECTIVE LAYER                             │
│           |  _  \                                                       │
│           |/  \  \                                                      │
│           `    \  \           ,--.    .-.          ,--.    .-.          │
│                 \  \         (/`\ \  //\)         (/`\ \  //\)          │
│                /    \            \ \//                \ \//             │
│               /  /\  \            \ (                  \ (              │
│              /  /  \  \           /, \                 /, \             │
│             /  /    \  \         // \ \               // \ \            │
│            /  /      \  \_     _//   \ \_,   .-.    _//   \ \_          │
│           /__/        \___)   |_/     \__/   \_/   |_/     \__/         │
│                                                                         │
│                                                                         │
│     This file specifies the effective interface of the development,     │
│     exposing   computational  content  together  with  input–output     │
│     contracts.   Each  computational  artifact  is  linked  to  its     │
│     semantic  interpretation  via  adequacy theorems. This layer is     │
│     machine-oriented   and   designed   to   remain   stable  under     │
│     extraction, testing, automation, and downstream reuse.              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)
 

(*
  Proofcase / E001 / IO Correctness
  =================================

    Overview
    --------

      This appendix file contains the logical properties of the executable IO
      layer. The runtime-facing definitions stay in `E001_99_IO`; this file
      keeps the image classification proofs and small sanity examples separate
      from the extracted interface.
*)

Require Import E001.E001_99_IO.

Lemma In_Imageb_true_iff :
  forall c,
    In_Imageb c = true <-> Check_Pairing c = c.
Proof.
  intro c.
  unfold In_Imageb.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

Corollary Check_Pairing_on_image :
  forall a b,
    Check_Pairing (Paired_AB a b) = Paired_AB a b.
Proof.
  intros a b.
  unfold Check_Pairing, Paired_AB, Unpaired_C.
  rewrite decode_encode.
  reflexivity.
Qed.

Corollary In_Imageb_on_image :
  forall a b,
    In_Imageb (Paired_AB a b) = true.
Proof.
  intros a b.
  apply In_Imageb_true_iff.
  apply Check_Pairing_on_image.
Qed.

Corollary Status_Of_Code_on_image :
  forall a b,
    Status_Of_Code (Paired_AB a b) = Part_Of_Injective_Function.
Proof.
  intros a b.
  unfold Status_Of_Code.
  rewrite In_Imageb_on_image.
  reflexivity.
Qed.

Lemma In_Imageb_true_iff_exists_pair :
  forall c,
    In_Imageb c = true <-> exists a b, c = Paired_AB a b.
Proof.
  intro c.
  split.
  - intro H.
    apply In_Imageb_true_iff in H.
    unfold Check_Pairing, Paired_AB, Unpaired_C in H.
    exists (fst (decode c)).
    exists (snd (decode c)).
    symmetry.
    exact H.
  - intros [a [b H]].
    subst c.
    apply In_Imageb_on_image.
Qed.

Lemma Status_Of_Code_part_iff :
  forall c,
    Status_Of_Code c = Part_Of_Injective_Function <->
    exists a b, c = Paired_AB a b.
Proof.
  intro c.
  split.
  - intro H.
    unfold Status_Of_Code in H.
    destruct (In_Imageb c) eqn:Himg.
    + apply In_Imageb_true_iff_exists_pair.
      exact Himg.
    + discriminate H.
  - intro H.
    unfold Status_Of_Code.
    destruct (In_Imageb c) eqn:Himg.
    + reflexivity.
    + exfalso.
      apply In_Imageb_true_iff_exists_pair in H.
      rewrite Himg in H.
      discriminate H.
Qed.

Lemma Status_Of_Code_dead_end_iff :
  forall c,
    Status_Of_Code c = Dead_End <->
    ~ exists a b, c = Paired_AB a b.
Proof.
  intro c.
  split.
  - intro Hdead.
    intro Hpair.
    assert (Hpart : Status_Of_Code c = Part_Of_Injective_Function).
    { apply Status_Of_Code_part_iff.
      exact Hpair. }
    rewrite Hdead in Hpart.
    discriminate Hpart.
  - intro Hnot.
    unfold Status_Of_Code.
    destruct (In_Imageb c) eqn:Himg.
    + exfalso.
      apply Hnot.
      apply In_Imageb_true_iff_exists_pair.
      exact Himg.
    + reflexivity.
Qed.

Example pair_io_3_5 :
  E001_IO (Pair_Query 3 5) = Pair_Result (Paired_AB 3 5).
Proof. reflexivity. Qed.

Example inspect_io_on_image :
  E001_IO (Inspect_Query (Paired_AB 3 5)) =
  Inspect_Result (3, 5) (Paired_AB 3 5) Part_Of_Injective_Function.
Proof.
  unfold E001_IO, Unpair_IO, Check_Pairing, Status_Of_Code, In_Imageb.
  unfold Paired_AB, Unpaired_C.
  rewrite decode_encode.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Redirect "theories/E001/appendix/assumptions/e001_io_correctness"
  Print Assumptions Status_Of_Code_dead_end_iff.
