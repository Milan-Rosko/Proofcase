(*A001_94_IO.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                            Proofcase / A001_94_IO                            │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Extraction-facing IO surface for A001. We provide two commands: one pairs
  an input `(A, B)`; the other inspects a code `C` by decoding it,
  re-encoding the resulting pair, and classifying whether `C` is already a
  canonical image point.

*)

From A001 Require Export A001_05__Pair_Unpair_Correct.

(*
│
│          The executable query type exposes pairing and code
│          inspection as the two commands.
│
*)

Inductive IO_Query : Type :=
| Pair_Query : nat -> nat -> IO_Query
| Inspect_Query : nat -> IO_Query.

(*
│
│          The inspection status distinguishes canonical image points
│          from non-canonical codes.
│
*)

Inductive Code_Status : Type :=
| Part_Of_Injective_Function
| Dead_End.

(*
│
│          The executable result type returns either a paired code or
│          the decoded inspection data for a single code.
│
*)

Inductive IO_Result : Type :=
| Pair_Result : nat -> IO_Result
| Inspect_Result : nat * nat -> nat -> Code_Status -> IO_Result.

(*
│
│          `Paired_AB` names the certified encoder for the IO surface.
│
*)

Definition Paired_AB : nat -> nat -> nat :=
  encode.

(*
│
│          `Unpaired_C` names the certified decoder for the IO
│          surface.
│
*)

Definition Unpaired_C : nat -> nat * nat :=
  decode.

(*    Check_Pairing(c) = Paired_AB(π₁(Unpaired_C(c)), π₂(Unpaired_C(c))).     *)

Definition Check_Pairing (c : nat) : nat :=
  let ab := Unpaired_C c in
  Paired_AB (fst ab) (snd ab).

(*
│
│          Image membership is decided by a fixed-point test: a code
│          is canonical exactly when decoding followed by re-encoding
│          returns the same number.
│
*)

(*                In_Imageb(c) = true ⇔ Check_Pairing(c) = c.                 *)

Definition In_Imageb (c : nat) : bool :=
  Nat.eqb (Check_Pairing c) c.

(*  Status_Of_Code(c) = Part_Of_Injective_Function, if In_Imageb(c) = true.   *)
(*           Status_Of_Code(c) = Dead_End, if In_Imageb(c) = false.           *)

Definition Status_Of_Code (c : nat) : Code_Status :=
  if In_Imageb c
  then Part_Of_Injective_Function
  else Dead_End.

(*
│
│          `Pair_IO` packages the paired code for a pair query.
│
*)

Definition Pair_IO (a b : nat) : IO_Result :=
  Pair_Result (Paired_AB a b).

(*
│
│          The inspection output bundles the decoded pair, its
│          re-encoding, and the image-status judgement for the queried
│          code.
│
*)

Definition Unpair_IO (c : nat) : IO_Result :=
  Inspect_Result (Unpaired_C c) (Check_Pairing c) (Status_Of_Code c).

(*
│
│          `A001_IO` dispatches pairing and inspection queries through
│          the certified pairing surface.
│
*)

Definition A001_IO (q : IO_Query) : IO_Result :=
  match q with
  | Pair_Query a b => Pair_IO a b
  | Inspect_Query c => Unpair_IO c
  end.

(*
│
│          The pair–inspect–check diagnostic returns the encoded pair,
│          its decoded form, its re-encoding, and its image status.
│
*)

Definition Compute_Pair_Unpair_Check (a b : nat)
  : nat * (nat * nat) * nat * Code_Status :=
  let c := Paired_AB a b in
  (c, Unpaired_C c, Check_Pairing c, Status_Of_Code c).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             COMPACT INTEGER VIEW                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `Paired_AB_Z` returns the paired code as a binary integer.
│
*)

Definition Paired_AB_Z (a b : nat) : BinNums.Z :=
  Z.of_nat (Paired_AB a b).

(*
│
│          `Unpaired_C_Z` returns the decoded pair as binary integers.
│
*)

Definition Unpaired_C_Z (c : nat) : BinNums.Z * BinNums.Z :=
  let ab := Unpaired_C c in
  (Z.of_nat (fst ab), Z.of_nat (snd ab)).

(*
│
│          `Check_Pairing_Z` returns the re-encoded inspection code as
│          a binary integer.
│
*)

Definition Check_Pairing_Z (c : nat) : BinNums.Z :=
  Z.of_nat (Check_Pairing c).

(*
│
│          The compact result type mirrors `IO_Result`, but stores
│          numeric payloads as binary integers.
│
*)

Inductive IO_Result_Z : Type :=
| Pair_Result_Z : BinNums.Z -> IO_Result_Z
| Inspect_Result_Z : BinNums.Z * BinNums.Z -> BinNums.Z -> Code_Status -> IO_Result_Z.

(*
│
│          `Pair_IO_Z` packages a pair query result in compact integer
│          form.
│
*)

Definition Pair_IO_Z (a b : nat) : IO_Result_Z :=
  Pair_Result_Z (Paired_AB_Z a b).

(*
│
│          `Unpair_IO_Z` packages an inspection result in compact
│          integer form.
│
*)

Definition Unpair_IO_Z (c : nat) : IO_Result_Z :=
  Inspect_Result_Z (Unpaired_C_Z c) (Check_Pairing_Z c) (Status_Of_Code c).

(*
│
│          `A001_IO_Z` dispatches the compact integer view of the
│          executable interface.
│
*)

Definition A001_IO_Z (q : IO_Query) : IO_Result_Z :=
  match q with
  | Pair_Query a b => Pair_IO_Z a b
  | Inspect_Query c => Unpair_IO_Z c
  end.

(*
│
│          The compact diagnostic returns the full pair–inspect–check
│          tuple, with numeric payloads in binary-integer form.
│
*)

Definition Compute_Pair_Unpair_Check_Z (a b : nat)
  : BinNums.Z * (BinNums.Z * BinNums.Z) * BinNums.Z * Code_Status :=
  let c := Paired_AB a b in
  (Paired_AB_Z a b, Unpaired_C_Z c, Check_Pairing_Z c, Status_Of_Code c).
