(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[We expose herein the executable dispatcher over a concrete pairing device: either pair an input `(A,B)`, or inspect a code `C` by decoding it, re-encoding the decoded pair, and classifying `C` as either an actual image point or a dead end.]]@*)

(*@genre.io@*)
(*@head.end@*)

From A001 Require Export A001_03__Pair_Unpair_Correct.

Inductive IO_Query : Type :=
| Pair_Query : nat -> nat -> IO_Query
| Inspect_Query : nat -> IO_Query.

Inductive Code_Status : Type :=
| Part_Of_Injective_Function
| Dead_End.

Inductive IO_Result : Type :=
| Pair_Result : nat -> IO_Result
| Inspect_Result : nat * nat -> nat -> Code_Status -> IO_Result.

Definition Paired_AB : nat -> nat -> nat :=
  encode.

Definition Unpaired_C : nat -> nat * nat :=
  decode.

(*@unicodemath@[[Check_Pairing(c) = Paired_AB(π₁(Unpaired_C(c)), π₂(Unpaired_C(c)))]]@*)

Definition Check_Pairing (c : nat) : nat :=
  let ab := Unpaired_C c in
  Paired_AB (fst ab) (snd ab).

(*@inline@[[We test image membership by a fixed-point criterion: a code belongs to the realized pairing graph exactly when decoding and re-encoding return the same natural number.]]@*)

Definition In_Imageb (c : nat) : bool :=
  Nat.eqb (Check_Pairing c) c.

(*@unicodemath@[[Status_Of_Code(c) = Part_Of_Injective_Function, if In_Imageb(c) = true]][[Status_Of_Code(c) = Dead_End, if In_Imageb(c) = false]]@*)

Definition Status_Of_Code (c : nat) : Code_Status :=
  if In_Imageb c
  then Part_Of_Injective_Function
  else Dead_End.

Definition Pair_IO (a b : nat) : IO_Result :=
  Pair_Result (Paired_AB a b).

(*@inline@[[We package the inspection output as a small certificate: the decoded pair, its repaired re-encoding, and the corresponding image-status judgment for the queried code.]]@*)

Definition Unpair_IO (c : nat) : IO_Result :=
  Inspect_Result (Unpaired_C c) (Check_Pairing c) (Status_Of_Code c).

Definition A001_IO (q : IO_Query) : IO_Result :=
  match q with
  | Pair_Query a b => Pair_IO a b
  | Inspect_Query c => Unpair_IO c
  end.

Definition Compute_Pair_Unpair_Check (a b : nat)
  : nat * (nat * nat) * nat * Code_Status :=
  let c := Paired_AB a b in
  (c, Unpaired_C c, Check_Pairing c, Status_Of_Code c).

(*@inline@[[Direct `Compute (Pair_IO 12 33)` overflows because Rocq tries to print `Pair_Result` with a Peano `nat` of size 601965. Use the compact `*_Z` views for interactive evaluation.]]@*)

Definition Paired_AB_Z (a b : nat) : BinNums.Z :=
  Z.of_nat (Paired_AB a b).

Definition Unpaired_C_Z (c : nat) : BinNums.Z * BinNums.Z :=
  let ab := Unpaired_C c in
  (Z.of_nat (fst ab), Z.of_nat (snd ab)).

Definition Check_Pairing_Z (c : nat) : BinNums.Z :=
  Z.of_nat (Check_Pairing c).

Inductive IO_Result_Z : Type :=
| Pair_Result_Z : BinNums.Z -> IO_Result_Z
| Inspect_Result_Z : BinNums.Z * BinNums.Z -> BinNums.Z -> Code_Status -> IO_Result_Z.

Definition Pair_IO_Z (a b : nat) : IO_Result_Z :=
  Pair_Result_Z (Paired_AB_Z a b).

Definition Unpair_IO_Z (c : nat) : IO_Result_Z :=
  Inspect_Result_Z (Unpaired_C_Z c) (Check_Pairing_Z c) (Status_Of_Code c).

Definition A001_IO_Z (q : IO_Query) : IO_Result_Z :=
  match q with
  | Pair_Query a b => Pair_IO_Z a b
  | Inspect_Query c => Unpair_IO_Z c
  end.

(*@inline@[[We bundle the full pair-inspect-repair diagnostic in compact integer form so that large examples can be evaluated interactively without expanding enormous Peano numerals. Keep the sample `vm_compute` probes disabled during normal compilation so imports of this file do not eagerly re-run them.]]@*)

Definition Compute_Pair_Unpair_Check_Z (a b : nat)
  : BinNums.Z * (BinNums.Z * BinNums.Z) * BinNums.Z * Code_Status :=
  let c := Paired_AB a b in
  (Paired_AB_Z a b, Unpaired_C_Z c, Check_Pairing_Z c, Status_Of_Code c).

(*
        Eval vm_compute in (Unpair_IO_Z (Paired_AB 12 33)).
        Eval vm_compute in (Check_Pairing_Z (Paired_AB 12 33)). 
        Eval vm_compute in (Unpair_IO_Z (Paired_AB 12 33)).
        Eval vm_compute in (A001_IO_Z (Inspect_Query (Paired_AB 12 33))). 
        Eval vm_compute in (Compute_Pair_Unpair_Check_Z 12 33).
*)
