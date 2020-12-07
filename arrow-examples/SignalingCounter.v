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


Require Import Cava.Arrow.ArrowExport.
Require Import Coq.Lists.List Coq.NArith.NArith Coq.Strings.String Bool.Bvector.
Import ListNotations.

Local Open Scope string_scope.

Section notation.
  Import KappaNotation.
  Local Open Scope category_scope.
  Local Open Scope kind_scope.

  Notation nibble := (Vector Bit 4).

  Definition counter :=
    <[fun "counter" is_valid value : nibble =>
      letrec counter =
        if is_valid
        then counter +% value
        else counter in
      counter
    ]>.
End notation.

Open Scope kind_scope.

Require Import Cava.Netlist.

Definition signaling_counter_Interface :=
   sequentialInterface "signaling_counter" "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "is_valid" Signal.Bit
     ;mkPort "value" (Signal.Vec Signal.Bit 4)]
     [mkPort "count" (Signal.Vec Signal.Bit 4)] [].

Definition signaling_counter_netlist :=
  build_netlist (closure_conversion counter) "signaling_counter" ("is_valid", "value") "count".

(* first four cycles have 'is_valid = false' and should not increment the counter *)
Definition signaling_counter_tb_inputs : list (bool * Bvector 4) :=
  (repeat (false, N2Bv_sized 4 1) 4) ++ (repeat (true, N2Bv_sized 4 1) 4).

Definition signaling_counter_tb_expected_outputs : list (Bvector 4) :=
  unroll_circuit_evaluation (closure_conversion counter) signaling_counter_tb_inputs.

Lemma arrow_and_expr_counter_semantics_agree:
  (map Bv2N signaling_counter_tb_expected_outputs) =
  (map Bv2N (interp_sequential ((counter : Kappa _ _) _) signaling_counter_tb_inputs)).
Proof. vm_compute; reflexivity. Qed.

Lemma expr_single_step_agree:
  (map Bv2N signaling_counter_tb_expected_outputs) =
  (map Bv2N (interp_sequential11 ((counter : Kappa _ _) _) signaling_counter_tb_inputs)).
Proof. vm_compute; reflexivity. Qed.

Definition bv_add s (av bv: Bvector s) :=
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    (Ndigits.N2Bv_sized s c).

(* List based specification *)
Fixpoint gallina_counter (state: Bvector 4) (inputs: list (bool * Bvector 4)): list (Bvector 4) :=
  match inputs with
  | [] => []
  | i :: is =>
    let '(is_valid, value) := i in
    let s := if is_valid then N2Bv_sized _ (Bv2N value + Bv2N state) else state in
    s :: gallina_counter s is
  end.



Lemma spec_and_kappa_agree_on_given:
  (map Bv2N (interp_sequential ((counter : Kappa _ _) _) signaling_counter_tb_inputs)) =
  (map Bv2N (gallina_counter (N2Bv_sized _ 0) signaling_counter_tb_inputs)).
Proof. vm_compute; reflexivity. Qed.

Lemma kappa_counter_is_gallina_counter: forall is,
  gallina_counter (N2Bv_sized _ 0) is =
  interp_sequential ((counter : Kappa _ _) _) is.
Proof.
  intros.
  induction is; [auto|].
  (* This goal should be true, otherwise bug in spec/semantics*)
  (* gallina_counter (a :: is) = interp_sequential (counter list_func) (a :: is) *)
Admitted.

(* Single step specification *)
Definition gallina_counter_single_step1
  (state: Bvector 4) (is_valid : bool) (value: Bvector 4): Bvector 4 :=
  if is_valid then N2Bv_sized 4 (Bv2N value + Bv2N state) else state.

Lemma singlestep_agree_on_a_point:
  snd (interp_sequential1 ((counter : Kappa _ _) _) [] (true, N2Bv_sized _ 1)) =
  gallina_counter_single_step1 (N2Bv_sized _ 0) true (N2Bv_sized _ 1).
Proof. vm_compute; reflexivity. Qed.

Lemma kappa_counter_is_gallina_counter_single_step: forall is s,
  gallina_counter_single_step1 s (fst is) (snd is) =
  snd (interp_sequential1 ((counter : Kappa _ _) _) [existT _ (Vector Bit 4) s] is).
Proof.
  intros.
  destruct is.
  cbv [gallina_counter_single_step1
    interp_sequential1 interp_sequential1' interp_combinational'
    counter coq_func denote_apply_rightmost_tt denote_kind module_to_expr module_body
    fst snd
    mux_item enable KappaNotation.unsigned_add1 replicate map2 bitwise
    primitive_output primitive_semantics binary_semantics unary_semantics nullary_semantics
    app bv_add kind_default].

  (* some vector expression that should be true*)
Admitted.

Definition signaling_counter_tb :=
  testBench "signaling_counter_tb" signaling_counter_Interface
            signaling_counter_tb_inputs signaling_counter_tb_expected_outputs.

