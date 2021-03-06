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
   Coq for the specification, implementaiton and formal verification of circuits.
   Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Numbers.BinNums.
From Coq Require Import ZArith.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Export ExtLib.Data.Monads.StateMonad.
Export MonadNotation.

Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Generalizable All Variables.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava m bit `{Monad m} := {
  (* Constant values. *)
  zero : m bit; (* This component always returns the value 0. *)
  one : m bit; (* This component always returns the value 1. *)
  delayBit : bit -> m bit; (* Cava bit-level unit delay. *)
  loopBit : forall {A B : Type}, ((A * bit)%type -> m (B * bit)%type) -> A -> m B;
  (* Primitive gates *)
  inv : bit -> m bit;
  and2 : bit * bit -> m bit;
  nand2 : bit * bit -> m bit;
  or2 : bit * bit -> m bit;
  nor2 : bit * bit -> m bit;
  xor2 : bit * bit -> m bit;
  xnor2 : bit * bit -> m bit;
  buf_gate : bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'buf' *)
  (* Xilinx UNISIM FPGA gates *)
  lut1 : (bool -> bool) -> bit -> m bit; (* 1-input LUT *)
  lut2 : (bool -> bool -> bool) -> (bit * bit) -> m bit; (* 2-input LUT *)
  lut3 : (bool -> bool -> bool -> bool) -> (bit * bit * bit) -> m bit; (* 3-input LUT *)
  lut4 : (bool -> bool -> bool -> bool -> bool) -> (bit * bit * bit * bit) ->
         m bit; (* 4-input LUT *)
  lut5 : (bool -> bool -> bool -> bool -> bool -> bool) ->
         (bit * bit * bit * bit * bit) -> m bit; (* 5-input LUT *)
  lut6 : (bool -> bool -> bool -> bool -> bool -> bool -> bool) ->
         (bit * bit * bit * bit * bit * bit) -> m bit; (* 6-input LUT *)
  xorcy : bit * bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, LI *)
  muxcy : bit -> bit -> bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, DI, S *)
  (* Synthesizable arithmetic operations. *)
  unsignedAdd : list bit -> list bit -> m (list bit);
}.

(******************************************************************************)
(* Netlist implementations for the Cava class.                                *)
(******************************************************************************)

Definition invNet (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindNot i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition andNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindAnd [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition nandNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindNand [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition orNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindOr [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition norNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindNor [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition xorNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindXor [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

(******************************************************************************)
(* Xilinx specific FPGA gates                                                 *)
(******************************************************************************)

Local Open Scope N_scope.

Definition lut1Net (f : bool -> bool) (i : N) : state CavaState N :=
  let config := N.b2n (f false) + 2 * N.b2n (f true) in
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindLut1 config i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition lut2Net (f : bool -> bool -> bool) (i : N * N) : state CavaState N :=
  let config :=     N.b2n (f false false) +
                2 * N.b2n (f true false) +
                4 * N.b2n (f false true) + 
                8 * N.b2n (f true true) in
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindLut2 config i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition f3List (f: bool -> bool -> bool -> bool) (l: list bool) : bool :=
  match l with
  | [a; b; c] => f a b c
  | _ => false
  end.

Definition lut3Net (f : bool -> bool -> bool -> bool) (i : N * N * N) :
                   state CavaState N :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 3 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f3List f bv)) (seq 0 8)  in
  let config := fold_left N.add powers 0 in 
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindLut3 config i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition f4List (f: bool -> bool -> bool -> bool -> bool) (l: list bool) :
  bool :=
  match l with
  | [a; b; c; d] => f a b c d
  | _ => false
  end.

Definition lut4Net (f : bool -> bool -> bool -> bool -> bool)
                  (i : N * N * N * N) : state CavaState N :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 4 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f4List f bv)) (seq 0 16)  in
  let config := fold_left N.add powers 0 in 
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindLut4 config i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition f5List (f: bool -> bool -> bool -> bool -> bool -> bool)
                  (l: list bool) : bool :=
  match l with
  | [a; b; c; d; e] => f a b c d e
  | _ => false
  end.

Definition lut5Net (f : bool -> bool -> bool -> bool -> bool -> bool)
                  (i : N * N * N * N * N) : state CavaState N :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 5 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f5List f bv)) (seq 0 32)  in
  let config := fold_left N.add powers 0 in 
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindLut5 config i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition f6List (fn: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                  (l: list bool) : bool :=
  match l with
  | [a; b; c; d; e; f] => fn a b c d e f
  | _ => false
  end.

Definition lut6Net (f : bool -> bool -> bool -> bool -> bool -> bool -> bool)
                  (i : N * N * N * N * N * N) : state CavaState N :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 6 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f6List f bv)) (seq 0 64)  in
  let config := fold_left N.add powers 0 in 
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindLut6 config i o) insts) inputs outputs )) ;;
         ret o
  end.

Local Close Scope N_scope.

Definition xorcyNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindXorcy i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition xnorNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindXnor [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition bufNet (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindBuf i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition muxcyNet (s : N) (ci : N) (di : N)  : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindMuxcy (s,(ci,di)) o) insts) inputs outputs )) ;;
         ret o
  end.

Definition unsignedAddNet (a : list N) (b : list N) :
                          state CavaState (list N) :=
  let sumSize := max (length a) (length b) + 1 in
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => let outv := map N.of_nat (seq (N.to_nat o) sumSize) in
         put (mkCavaState (o + (N.of_nat sumSize)) isSeq (mkModule name (cons (BindUnsignedAdd sumSize (a, b) outv) insts) inputs outputs )) ;;
         ret outv
  end.

Definition delayBitNet (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) true (mkModule name (cons (BindDelayBit i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition loopBitNet (A B : Type) (f : (A * N)%type -> state CavaState (B * N)%type) (a : A) : state CavaState B :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name insts inputs outputs)) ;;
         '(b, cOut) <- f (a, o) ;;
          cs2 <- get ;;
          match cs2 with
          | mkCavaState o2 isSeq (mkModule name insts inputs outputs)
              => put (mkCavaState (o2+1) isSeq (mkModule name (cons (BindAssignBit o cOut) insts) inputs outputs)) ;;
                 ret b
          end
  end.

(******************************************************************************)
(* Instantiate the Cava class for CavaNet which describes circuits without    *)
(* any top-level pins or other module-level data                              *)
(******************************************************************************)

Instance CavaNet : Cava (state CavaState) N :=
  { zero := ret 0%N;
    one := ret 1%N;
    delayBit := delayBitNet;
    loopBit a b := loopBitNet a b;
    inv := invNet;
    and2 := andNet;
    nand2 := nandNet;
    or2 := orNet;
    nor2 := norNet;
    xor2 := xorNet;
    xnor2 := xorNet;
    buf_gate := bufNet;
    lut1 := lut1Net;
    lut2 := lut2Net;
    lut3 := lut3Net;
    lut4 := lut4Net;
    lut5 := lut5Net;
    lut6 := lut6Net;
    xorcy := xorcyNet;
    muxcy := muxcyNet;
    unsignedAdd := unsignedAddNet;
}.

(******************************************************************************)
(* Define netlist functions used to specify top-level module behaviour.       *)
(******************************************************************************)

Definition setModuleName (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule _ insts inputs outputs)
     => put (mkCavaState o isSeq (mkModule name insts inputs outputs))
  end.

Definition inputBit (name : string) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let newPort := mkPort name Bit in
        let insts' := BindPrimitive (WireInputBit name) tt o :: insts in
        put (mkCavaState (o+1) isSeq (mkModule n insts' (cons newPort inputs) outputs)) ;;
        ret o
  end.

Definition inputVectorTo0 (sizes : list nat) (name : string) : state CavaState (@bitVecTy nat N sizes) :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let netNumbers := numberBitVec o sizes sizes in
        let newPort := mkPort name (BitVec sizes) in
        let portInst := BindPrimitive (WireInputBitVec name) tt netNumbers in
        let netsUsed := fold_left (fun x y => x * y) sizes 1 in
        put (mkCavaState (o + (N.of_nat netsUsed)) isSeq (mkModule n (portInst :: insts) (newPort :: inputs) outputs)) ;;
        ret netNumbers
  end.

Definition outputBit (name : string) (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let newPort := mkPort name Bit in
        let insts' := BindPrimitive (WireOutputBit name) i tt :: insts in
        put (mkCavaState o isSeq (mkModule n insts' inputs (newPort :: outputs))) ;;
        ret i
  end.

Definition outputVectorTo0 (sizes : list nat) (v : @bitVecTy nat N sizes) (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let newPort := mkPort name (BitVec sizes) in
        let insts' := BindPrimitive (WireOutputBitVec name) v tt :: insts in
        put (mkCavaState o isSeq (mkModule n insts' inputs (newPort :: outputs))) ;;
        ret tt
  end.

(******************************************************************************)
(* Execute a monadic circuit description and return the generated netlist.    *)
(******************************************************************************)

Definition instantiateInputPort (pd : PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match pd with
  | mkPort name Bit => _ <- inputBit name ;; ret tt
  | mkPort name (BitVec xs) => _ <- inputVectorTo0 xs name ;; ret tt
  end.

Fixpoint instantiateInputPorts (ports : list PortDeclaration) : state CavaState unit :=
  match ports with
  | [] => ret tt
  | p::ps => instantiateInputPort p ;;
             instantiateInputPorts ps
  end.

Definition instantiateOutputPort (pd : PortDeclaration) (outputNetNumbers : list N)
                                 : state CavaState unit :=
  cs <- get ;;
  match pd with
  | mkPort name Bit => _ <- outputBit name (hd 0%N outputNetNumbers) ;; ret tt
  | mkPort name (BitVec [n]) => _ <- outputVectorTo0 [n] (firstn n outputNetNumbers) name ;; ret tt
  | _ => ret tt
  end.

Fixpoint instantiateOutputPorts (ports : list PortDeclaration) (outputNetNumbers : list N)
                                : state CavaState unit :=
  match ports with
  | [] => ret tt
  | p::ps => instantiateOutputPort p outputNetNumbers ;;
             instantiateOutputPorts ps (skipn (bitsInPort (port_shape p)) outputNetNumbers)
  end.

Definition wireUpCircuit (intf : CircuitInterface)
                         `{Flatten (signalTy N (mapShape snd (circuitOutputs intf)))}
                         (circuit : (signalTy N (mapShape snd (circuitInputs intf))) ->
                                    state CavaState (signalTy N (mapShape snd (circuitOutputs intf))))
                         : state CavaState unit  :=
  setModuleName (circuitName intf) ;;
  cs <- get ;;
  let countInputsFrom := netNumber cs in
  let inputPort : @shape (string * portType) := circuitInputs intf in
  let typeShape : @shape portType := mapShape snd inputPort in
  let numberedInputs : signalTy N typeShape := numberPort countInputsFrom typeShape in
  instantiateInputPorts (shapeToPortDeclaration inputPort) ;;
  o <- circuit numberedInputs ;;
  let outputNetNumbers := flatten o in
  instantiateOutputPorts (shapeToPortDeclaration (circuitOutputs intf)) outputNetNumbers.

Definition makeNetlist (intf : CircuitInterface)
                       `{Flatten (signalTy N (mapShape snd (circuitOutputs intf)))}
                       (circuit : signalTy N (mapShape snd (circuitInputs intf)) ->
                                  state CavaState (signalTy N (mapShape snd (circuitOutputs intf)))) : CavaState
  := execState (wireUpCircuit intf circuit) initState.

(******************************************************************************)
(* A second boolean combinational logic interpretaiob for the Cava class      *)
(******************************************************************************)

Definition notBool (i: bool) : ident bool :=
  ret (negb i).

Definition andBool '(a, b) : ident bool :=
  ret (a && b).

Definition nandBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (a && b)).

Definition orBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (a || b).

Definition norBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (a || b)).

Definition xorBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (xorb a b).

Definition xnorBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (xorb a b)).

Definition lut1Bool (f: bool -> bool) (i: bool) : ident bool := ret (f i).

Definition lut2Bool (f: bool -> bool -> bool) (i: bool * bool) : ident bool :=
  ret (f (fst i) (snd i)).

Definition lut3Bool (f: bool -> bool -> bool -> bool) (i: bool * bool * bool) :
                    ident bool :=
  let '(i0, i1, i2) := i in
  ret (f i0 i1 i2).

Definition lut4Bool (f: bool -> bool -> bool -> bool -> bool)
                    (i: bool * bool * bool * bool) : ident bool :=
  let '(i0, i1, i2, i3) := i in
  ret (f i0 i1 i2 i3).

Definition lut5Bool (f: bool -> bool -> bool -> bool -> bool -> bool)
                    (i: bool * bool * bool * bool * bool) : ident bool :=
  let '(i0, i1, i2, i3, i4) := i in
  ret (f i0 i1 i2 i3 i4).

Definition lut6Bool (f: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                    (i: bool * bool * bool * bool * bool * bool) : ident bool :=
  let '(i0, i1, i2, i3, i4, i5) := i in
  ret (f i0 i1 i2 i3 i4 i5).

Definition xorcyBool (i: bool * bool) : ident bool :=
  let (ci, li) := i in ret (xorb ci li).

Definition muxcyBool (s : bool) (ci : bool) (di : bool) : ident bool :=
  ret (match s with
       | false => di
       | true => ci
       end).

Definition unsignedAddBool (av : list bool) (bv : list bool) :
                           ident (list bool) :=
  let a := list_bits_to_nat av in
  let b := list_bits_to_nat bv in
  let sumSize := max (length av) (length bv) + 1 in
  let sum := (a + b)%N in
  ret (nat_to_list_bits_sized sumSize sum).

Definition bufBool (i : bool) : ident bool :=
  ret i.

Definition loopBitBool (A B : Type) (f : A * bool -> ident (B * bool)) (a : A) : ident B :=
  '(b, _) <- f (a, false) ;;
  ret b.

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

Instance CavaBool : Cava ident bool :=
  { zero := ret false;
    one := ret true;
    delayBit i := ret i; (* Dummy definition for delayBit for now. *)
    loopBit a b := loopBitBool a b;
    inv := notBool;
    and2 := andBool;
    nand2 := nandBool;
    or2 := orBool;
    nor2 := norBool;
    xor2 := xorBool;
    lut1 := lut1Bool;
    lut2 := lut2Bool;
    lut3 := lut3Bool;
    lut4 := lut4Bool;
    lut5 := lut5Bool;
    lut6 := lut6Bool;
    xorcy := xorcyBool;
    xnor2 := xnorBool;
    muxcy := muxcyBool;
    unsignedAdd m n := @unsignedAddBool m n;
    buf_gate := bufBool;
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition combinational {a} (circuit : ident a) : a := unIdent circuit.

(******************************************************************************)
(* A list-based sequential logic interpretaion for the Cava class      *)
(******************************************************************************)

Definition notBoolList (i : list bool) : ident (list bool) :=
  ret (map negb i).

Definition andBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in a && b) (combine (fst i) (snd i))).

Definition nandBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in negb (a && b)) (combine (fst i) (snd i))).

Definition orBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in a || b) (combine (fst i) (snd i))).

Definition norBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in negb (a || b)) (combine (fst i) (snd i))).

Definition xorBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in xorb a b) (combine (fst i) (snd i))).

Definition lut1BoolList (f: bool -> bool) (i : list bool) : ident (list bool) :=
  ret (map f i).

Definition lut2BoolList (f: bool -> bool -> bool)
                        (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in f a b)
           (combine (fst i) (snd i))).

Definition lut3BoolList (f: bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * (list bool)) : ident (list bool) :=
  let '(aL, bL, cL) := i in
  ret (map (fun (i : bool * bool * bool) => let '(a, b, c) := i in f a b c)
           (combine (combine aL bL) cL)).

Definition lut4BoolList (f: bool -> bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * 
                             (list bool) * (list bool)) : ident (list bool) :=
  let '(aL, bL, cL, dL) := i in
  ret (map (fun (i : bool * bool * bool * bool) =>
            let '(a, b, c, d) := i in f a b c d)
           (combine (combine (combine aL bL) cL) dL)).

Definition lut5BoolList (f: bool -> bool -> bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * (list bool) *
                             (list bool) * (list bool)) : ident (list bool) :=
  let '(aL, bL, cL, dL, eL) := i in
  ret (map (fun (i : bool * bool * bool * bool * bool) =>
            let '(a, b, c, d, e) := i in f a b c d e)
           (combine (combine (combine (combine aL bL) cL) dL) eL)).

Definition lut6BoolList (fn: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * (list bool) *
                             (list bool) * (list bool) * (list bool)) :
                        ident (list bool) :=
  let '(aL, bL, cL, dL, eL, fL) := i in
  ret (map (fun (i : bool * bool * bool * bool * bool * bool) =>
            let '(a, b, c, d, e, f) := i in fn a b c d e f)
           (combine (combine (combine (combine (combine aL bL) cL) dL) eL) fL)).

Definition xorcyBoolList := xorBoolList.

Definition xnorBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in negb (xorb a b)) (combine (fst i) (snd i))).

Definition muxcyBoolList (s : list bool) (ci : list bool) (di : list bool)  : ident (list bool) :=
  let dici := combine di ci in
  let s_dici := combine s dici in
  ret (map (fun (i : bool * (bool * bool)) =>
     let '(s, (ci, di)) := i in
     match s with
       | false => di
       | true => ci
     end) s_dici).

(* A dummy definition for unsignedAdd because I expect us to totally overhaul how
   we model sequential circuits.
   TODO(satnam): Replace with actual definition when sequential circuit semantics are clearer.
*)
Definition unsignedAddBoolList (a : list (list bool)) (b : list (list bool)) :
                               ident (list (list bool)) :=
  ret ([]).

Definition bufBoolList (i : list bool) : ident (list bool) :=
  ret i.

Definition loopBitBoolList (A B : Type) (f : A * list bool -> ident (B * list bool)) (a : A) : ident B :=
  '(b, _) <- f (a, [false]) ;;
  ret b.

Definition delayBitBoolList (i : list bool) : ident (list bool) :=
  ret (false :: i).

Instance CavaBoolList : Cava ident (list bool) :=
  { zero := ret [false];
    one := ret [true];
    delayBit := delayBitBoolList;
    loopBit := loopBitBoolList;
    inv := notBoolList;
    and2 := andBoolList;
    nand2 := nandBoolList;
    or2 := orBoolList;
    nor2 := norBoolList;
    xor2 := xorBoolList;
    lut1 := lut1BoolList;
    lut2 := lut2BoolList;
    lut3 := lut3BoolList;
    lut4 := lut4BoolList;
    lut5 := lut5BoolList;
    lut6 := lut6BoolList;
    xorcy := xorcyBoolList;
    xnor2 := xnorBoolList;
    muxcy := muxcyBoolList;
    unsignedAdd := unsignedAddBoolList;
    buf_gate := bufBoolList;
}.

Definition sequential {a} (circuit : ident (list a)) : list a := unIdent circuit.

