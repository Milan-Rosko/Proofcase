(*A002_02__Tagged_Lists.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / A002_02__Tagged_Lists                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Tagged-list layer for A002. We encode finite sequences as A001-canonical
  list nodes, provide bounded destructors, and define the exact-length check
  used by derivation bodies.

  All list destructuring is guarded by `canonical001b`. A non-canonical
  natural number that A001 can decode to a pair is rejected as a list node
  rather than silently normalized.

*)

From A002 Require Export A002_01__A001_Wrappers.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           TAGGED LIST CONSTRUCTORS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The nil tag marks the unique empty list node. Its payload
│          is fixed to `0`.
│
*)

Definition TAG_NIL : nat := 0.

(*
│
│          The cons tag marks a list node whose payload is an A001
│          pair containing the head and tail.
│
*)

Definition TAG_CONS : nat := 1.

(*
│
│          `code_nil` is the canonical tagged empty list.
│
*)

Definition code_nil : nat :=
  encode TAG_NIL 0.

(*
│
│          `code_cons h t` is the canonical tagged cons node with head
│          `h` and tail `t`. The tail is intentionally only a number
│          here; validity as a list is checked separately and
│          boundedly.
│
*)

Definition code_cons (h t : nat) : nat :=
  encode TAG_CONS (encode h t).

(*
│
│          A derivation header stores the claimed length together with
│          the tagged list body.
│
*)

Definition code_derivation (n body : nat) : nat :=
  encode n body.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               LIST NODE TESTS                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `list_tag` reads the tag exposed by A001 decoding. Later
│          code treats this projection as list structure only after
│          the enclosing node has passed the canonical A001 test.
│
*)

Definition list_tag (body : nat) : nat :=
  fst001 body.

(*
│
│          `list_payload` reads the payload exposed by A001 decoding.
│          Later code treats this projection as list payload only
│          after canonicity and tag checks have selected a valid list
│          constructor.
│
*)

Definition list_payload (body : nat) : nat :=
  snd001 body.

(*
│
│          The nil-node Boolean checks canonicity, the nil tag, and
│          the fixed nil payload.
│
*)

Definition is_nil_nodeb (body : nat) : bool :=
  is_pair001b body TAG_NIL 0.

(*
│
│          The cons-node Boolean checks only the outer node shape. The
│          head/tail payload is a second A001 pair and is checked
│          separately by `cons_payloadb`.
│
*)

Definition is_cons_nodeb (body : nat) : bool :=
  canonical001b body && Nat.eqb (list_tag body) TAG_CONS.

(*
│
│          `cons_payloadb` recognizes a canonical head/tail payload
│          under a cons node.
│
*)

Definition cons_payloadb (payload : nat) : bool :=
  canonical001b payload.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           BOUNDED LIST OPERATIONS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `list_exact_lengthb n body` inspects exactly `n` cons cells
│          and then requires the next node to be `code_nil`. It never
│          traverses beyond the claimed length.
│
*)

Fixpoint list_exact_lengthb (n body : nat) : bool :=
  match n with
  | 0 => is_nil_nodeb body
  | S n' =>
      if canonical001b body then
        if Nat.eqb (list_tag body) TAG_CONS then
          let payload := list_payload body in
          if cons_payloadb payload then
            list_exact_lengthb n' (snd001 payload)
          else false
        else false
      else false
  end.

(*
│
│          `nth_list_fuel fuel body i` returns the `i`-th list element
│          when found within the supplied fuel. Failure returns an
│          A002-coded arithmetic error.
│
*)

Fixpoint nth_list_fuel (fuel body i : nat) : nat :=
  match fuel with
  | 0 => reject STAGE_LIST_STRUCTURE i ERR_FUEL_EXHAUSTED
  | S fuel' =>
      if canonical001b body then
        let tag := list_tag body in
        let payload := list_payload body in
        if Nat.eqb tag TAG_CONS then
          if cons_payloadb payload then
            let h := fst001 payload in
            let t := snd001 payload in
            if Nat.eqb i 0 then
              accept h
            else
              nth_list_fuel fuel' t (Nat.pred i)
          else
            reject STAGE_LIST_STRUCTURE i ERR_NONCANONICAL_NODE
        else if Nat.eqb tag TAG_NIL then
          reject STAGE_LIST_STRUCTURE i ERR_INDEX_OUT_OF_RANGE
        else
          reject STAGE_LIST_STRUCTURE i ERR_BAD_LIST_TAG
      else
        reject STAGE_LIST_STRUCTURE i ERR_NONCANONICAL_NODE
  end.

(*
│
│          `nth_list` supplies a simple arithmetical fuel bound from
│          the requested index: finding index `i` requires at most `S
│          i` cons-node inspections.
│
*)

Definition nth_list (body i : nat) : nat :=
  nth_list_fuel (S i) body i.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CONSTRUCTOR FACTS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The canonical nil node passes the nil-node test.
│
*)

Lemma is_nil_nodeb_code_nil :
  is_nil_nodeb code_nil = true.
Proof.
  unfold is_nil_nodeb, code_nil.
  apply is_pair001b_encode.
Qed.

(*
│
│          Every constructed cons node is canonical at its outer tag.
│
*)

Lemma is_cons_nodeb_code_cons :
  forall h t, is_cons_nodeb (code_cons h t) = true.
Proof.
  intros h t.
  unfold is_cons_nodeb, code_cons, list_tag.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  apply Nat.eqb_refl.
Qed.

(*
│
│          The empty list has exact length zero.
│
*)

Lemma list_exact_lengthb_code_nil :
  list_exact_lengthb 0 code_nil = true.
Proof.
  cbn [list_exact_lengthb].
  apply is_nil_nodeb_code_nil.
Qed.

(*
│
│          Adding one constructed cons cell increments exact list
│          length.
│
*)

Lemma list_exact_lengthb_code_cons :
  forall n h t,
    list_exact_lengthb n t = true ->
    list_exact_lengthb (S n) (code_cons h t) = true.
Proof.
  intros n h t Hlen.
  cbn [list_exact_lengthb].
  unfold code_cons, list_tag, list_payload, cons_payloadb.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  rewrite snd001_encode.
  exact Hlen.
Qed.

(*
│
│          Index zero of a constructed cons node is its head.
│
*)

Lemma nth_list_fuel_code_cons_zero :
  forall fuel h t,
    nth_list_fuel (S fuel) (code_cons h t) 0 = accept h.
Proof.
  intros fuel h t.
  cbn [nth_list_fuel].
  unfold code_cons, list_tag, list_payload, cons_payloadb.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  reflexivity.
Qed.

(*
│
│          Successor indexing of a constructed cons node continues
│          with the tail and one less index.
│
*)

Lemma nth_list_fuel_code_cons_succ :
  forall fuel h t i,
    nth_list_fuel (S fuel) (code_cons h t) (S i) =
    nth_list_fuel fuel t i.
Proof.
  intros fuel h t i.
  cbn [nth_list_fuel].
  unfold code_cons, list_tag, list_payload, cons_payloadb.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite canonical001b_encode.
  rewrite Nat.eqb_refl.
  rewrite snd001_encode.
  reflexivity.
Qed.
