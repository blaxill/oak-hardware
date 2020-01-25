(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

(* Definitions used for nat level proofs about the full adder which are kept
   separate because they are not used for extraction to SystemVerilog.
*)

From Coq Require Import Bool.Bool. 
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Require Import Nat Arith Lia.
Import ListNotations.

Require Import Hask.Control.Monad.

Require Import Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

Require Import Cava.
Require Import FullAdder.
Require Import BitVector.

Lemma halfAdderNat :
  forall (a : nat) (b : nat), a < 2 -> b < 2 ->
  let (part_sum, carry_out) := combinational (halfAdder (nat2bool a) (nat2bool b)) in
  bits_to_nat [part_sum; carry_out] = a + b.
Proof.
  intro.
  case a, b.
  all : simpl.
  all: lia.
Qed.
  
Lemma fullAdderNat :
  forall (a : nat) (b : nat) (cin : nat), a < 2 -> b < 2 -> cin < 2 ->
  let (sum, carry_out) := combinational (fullAdder (nat2bool a) (nat2bool b) (nat2bool cin)) in
  bits_to_nat [sum; carry_out] = a + b + cin.
Proof.
  intros.
  case a, b, cin.
  all : simpl.
  all: lia.
Qed.