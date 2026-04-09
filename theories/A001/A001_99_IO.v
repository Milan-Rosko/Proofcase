(*A001_99_IO.v*)

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                Copyright and author remark. Author(s):  │
│             ╭╮╮╮─╮             Milan Rosko  https://www.milanrosko.com  │
│             ││││╭╯             Licence. This file is distributed under  │
│              ╯╯╯╰              the Mozilla Public License Version 2.0,  │
│                                visit https://www.mozilla.org/en-US/MPL  │
└─────────────────────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / A001_99_IO : I/O                       │
└─────────────────────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                                I/O LAYER                                │
│           _____                                                         │
│          ´  _  \                                                        │
│         ( /  \  \                                                       │
│          `    \  \            ,--.    ,-           ,--.    ,-           │
│                \  \          (_.\ \  //\_)        (_.\ \  //\_)         │
│               /    \             \ \//                \ \//             │
│              /  /\  \             \ (                  \ (              │
│             /  /  \  \            /, \                 /, \             │
│            /  /    \  \          // \ \               // \ \            │
│           /  /      \  \_,     _//   \ \_,   .-.    _//   \ \_,         │
│          /__/        \___/    (_/     \__/   ._.   (_/     \__/         │
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

From A001 Require Export A001_02__Pair_Unpair_Correct.

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

Definition Check_Pairing (c : nat) : nat :=
  let ab := Unpaired_C c in
  Paired_AB (fst ab) (snd ab).

Definition In_Imageb (c : nat) : bool :=
  Nat.eqb (Check_Pairing c) c.

Definition Status_Of_Code (c : nat) : Code_Status :=
  if In_Imageb c
  then Part_Of_Injective_Function
  else Dead_End.

Definition Pair_IO (a b : nat) : IO_Result :=
  Pair_Result (Paired_AB a b).

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

Definition Compute_Pair_Unpair_Check_Z (a b : nat)
  : BinNums.Z * (BinNums.Z * BinNums.Z) * BinNums.Z * Code_Status :=
  let c := Paired_AB a b in
  (Paired_AB_Z a b, Unpaired_C_Z c, Check_Pairing_Z c, Status_Of_Code c).

(*
│
│             Note that direct `Compute (Pair_IO 12 33)`
│             overflows as Rocq “tries” to print
│             `Pair_Result` with a Peano `nat` of size
│             601965. Use the compact `*_Z` views for
│             interactive evaluation.
│
*)

Eval vm_compute in (Unpair_IO_Z (Paired_AB 12 33)).
Eval vm_compute in (Check_Pairing_Z (Paired_AB 12 33)).
Eval vm_compute in (Unpair_IO_Z (Paired_AB 12 33)).
Eval vm_compute in (A001_IO_Z (Inspect_Query (Paired_AB 12 33))).
Eval vm_compute in (Compute_Pair_Unpair_Check_Z 12 33).

(*
│
│             We extract to OCaml.
│
*)

Extraction Language OCaml.
Extraction "carryless_pairing_io"
  A001_IO Pair_IO Unpair_IO
  Paired_AB Unpaired_C Check_Pairing In_Imageb Status_Of_Code.
