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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of
   circuits. Experimental work, very much in flux, as Satnam learns Coq!
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Arith.PeanoNat.
Require Import Omega.

From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.
Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Monad.UnsignedAdders.

Set Implicit Arguments.

(******************************************************************************)
(* A generic description of all adder trees made from a syntheszable adder    *)
(* by using the tree combinator.                                              *)
(******************************************************************************)

Definition adderTree {m bit} `{Cava m bit} := tree unsignedAdd.

(******************************************************************************)
(* Some tests.                                                                *)
(******************************************************************************)

Definition v0 := nat_to_list_bits_sized 8  4.
Definition v1 := nat_to_list_bits_sized 8 17.
Definition v2 := nat_to_list_bits_sized 8  6.
Definition v3 := nat_to_list_bits_sized 8  3.

Local Open Scope N_scope.
Local Open Scope string_scope.

(* An adder tree with 2 inputs. *)

Definition adderTree2 {m bit} `{Cava m bit} (v : list (list bit)) : m (list bit)
  := adderTree 0 v.

Definition v0_v1 := [v0; v1].
Definition v0_plus_v1 : list bool := combinational (adderTree 0 v0_v1).
Example sum_vo_v1 : list_bits_to_nat v0_plus_v1 = 21.
Proof. reflexivity. Qed.

(* An adder tree with 4 inputs. *)

Definition adderTree4 {m bit} `{Cava m bit} (v : list (list bit)) : m (list bit)
  := adderTree 1 v.

Definition v0_v1_v2_v3 := [v0; v1; v2; v3].
Definition adderTree4_v0_v1_v2_v3 : list bool := combinational (adderTree4 v0_v1_v2_v3).
Example sum_v0_v1_v2_v3 : list_bits_to_nat (combinational (adderTree4 v0_v1_v2_v3)) = 30.
Proof. reflexivity. Qed.

Local Open Scope nat_scope.

Definition adder_tree_Interface name nrInputs bitSize
  := mkCircuitInterface name
     (One ("inputs", BitVec [nrInputs; bitSize]))
     (One ("sum", BitVec [bitSize + nrInputs - 1]))
     [].

(* Create netlist and test-bench for a 4-input adder tree. *)

Definition adder_tree4_8Interface := adder_tree_Interface "adder_tree4_8" 4 8.

Definition adder_tree4_8Netlist
  := makeNetlist adder_tree4_8Interface adderTree4.

Local Open Scope N_scope.

Definition adder_tree4_8_tb_inputs
  := map (fun i => map (nat_to_list_bits_sized 8) i)
     [[17; 42; 23; 95]; [4; 13; 200; 30]; [255; 74; 255; 200]].

Definition adder_tree4_8_tb_expected_outputs
  := map (fun i => combinational (adderTree4 i)) adder_tree4_8_tb_inputs.

Definition adder_tree4_8_tb :=
  testBench "adder_tree4_8_tb" adder_tree4_8Interface
  adder_tree4_8_tb_inputs adder_tree4_8_tb_expected_outputs.

(* Create netlist for a 32-input adder tree. *)

Definition adder_tree32_8Interface := adder_tree_Interface "adder_tree32_8" 32 8.

Definition adder_tree32_8Netlist
  := makeNetlist adder_tree32_8Interface (adderTree 4).

(* Create netlist and test-bench for a 64-input adder tree. *)

Definition adder_tree64_8Interface := adder_tree_Interface "adder_tree64_8" 64 8.

Definition adder_tree64_8Netlist
  := makeNetlist adder_tree64_8Interface (adderTree 5).

Definition adder_tree64_8_tb_inputs
  := map (fun i => map (nat_to_list_bits_sized 8) i)
     (repeat 255 64 :: map (map N.of_nat)
     [seq 0 64; seq 64 64; seq 128 64]).

Definition adder_tree64_8_tb_expected_outputs
  := map (fun i => combinational (adderTree 5 i)) adder_tree64_8_tb_inputs.

Definition adder_tree64_8_tb :=
  testBench "adder_tree64_8_tb" adder_tree64_8Interface
  adder_tree64_8_tb_inputs adder_tree64_8_tb_expected_outputs.

(* Create netlist and test-bench for a 64-input adder tree adding 128-bit words. *)

Definition adder_tree64_128Interface := adder_tree_Interface "adder_tree64_128" 64 128.

Definition adder_tree64_128Netlist
  := makeNetlist adder_tree64_128Interface (adderTree 5).

Definition adder_tree64_128_tb_inputs
  := map (fun i => map (nat_to_list_bits_sized 128) i)
     (repeat (2^128-1) 64 :: map (map N.of_nat)
     [seq 0 64; seq 64 64; seq 128 64]).

Definition adder_tree64_128_tb_expected_outputs
  := map (fun i => combinational (adderTree 5 i)) adder_tree64_128_tb_inputs.

Definition adder_tree64_128_tb :=
  testBench "adder_tree64_128_tb" adder_tree64_128Interface
  adder_tree64_128_tb_inputs adder_tree64_128_tb_expected_outputs.

