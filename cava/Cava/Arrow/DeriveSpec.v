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

Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Arrow.ArrowExport.

(* This file contains tactics and notations designed to simplify proofs that
   derive or prove specifications for kappa-level circuits. *)

Lemma reduce_module_match i o (f: ModuleK i o):
  interp_combinational' ((f: Kappa _ _) coq_func) =
  match f with
  | {| module_body := m |} => interp_combinational' (m coq_func)
  end .
Proof. now destruct f. Qed.

Ltac kappa_spec_begin :=
  intros; cbn [interp_combinational'
    denote_apply_rightmost_tt
    fst snd
  ];
  repeat match goal with
         | |- context [primitive_semantics ?p] =>
           let x := constr:(primitive_semantics p) in
           let y := (eval cbv [primitive_semantics nullary_semantics unary_semantics binary_semantics] in x) in
           progress change x with y
         | _ => progress cbn [denote_kind primitive_input primitive_output
           nullary_semantics unary_semantics binary_semantics]
         end; fold denote_kind in *.

Create HintDb kappa_interp discriminated.

Ltac kappa_spec_step :=
  match goal with
  | |- context E [ interp_combinational' ((module_to_expr {| module_body := ?X |}) coq_func) ]
    =>
      change (interp_combinational' ((module_to_expr {| module_body := X |}) coq_func))
        with (interp_combinational' (X coq_func))
      ; kappa_spec_begin

  | |- context E [ match ?f with _ => _ end ] =>
    replace (match f with _ => _ end) with (kinterp f)
    (* ; [|apply reduce_module_match] -- sometimes replace fails to replace the right thing?
      instead catch an incorrect replace and fall back to the slower 'change' *)
    ; [|
    lazymatch goal with
    | |- context[match _ with _ => _ end] => idtac
    | |- _ => (* idtac "no match found in generated equality?!"; *) fail
    end
    ; apply reduce_module_match]
  | |- context E [ match ?f with _ => _ end ] =>
    let E' := context E [kinterp f] in change E'

  | H : context [interp_combinational' (_ coq_func) _ = _] |- _ => rewrite H by eauto
  | _ => progress (autorewrite with kappa_interp)
  | |- context [interp_combinational'] => kappa_spec_begin
  end.
Ltac kappa_spec := kappa_spec_begin; repeat kappa_spec_step.

Ltac derive_spec_done :=
  lazymatch goal with
  | |- context [interp_combinational' ?x] =>
    fail "derived spec still contains disallowed term: interp_combinational'" x
  | _ => idtac
  end;
  repeat match goal with
         | x := _ |- _ => subst x
         end;
  (instantiate_app_by_reflexivity || reflexivity).
Ltac derive_spec_simplify :=
  repeat match goal with
         | |- context [let '(x, _) := ?p in x] =>
           change (let '(x, _) := p in x) with (fst p)
         | |- context [let '(_, x) := ?p in x] =>
           change (let '(_, x) := p in x) with (snd p)
         end.
Ltac derive_spec :=
  match goal with
  | |- context [interp_combinational'] => idtac
  | |- ?x => fail "goal does not include interp_combinational:" x
  end;
  intros; derive_spec_simplify; kappa_spec; derive_spec_done.

Ltac derive_map_spec :=
  match goal with
  | |- context [Vector.map ?f] =>
    match f with
    | context [interp_combinational'] => idtac
    end;
    match type of f with
    | ?t =>
      let g := fresh "g" in
      evar (g:t);
      erewrite (Vector.map_ext _ _ f g) by derive_spec
    end
  end.

Ltac derive_foldl_spec :=
  match goal with
  | |- context [Vector.fold_left ?f] =>
    match f with
    | context [interp_combinational'] => idtac
    end;
    match type of f with
    | ?t =>
      let g := fresh "g" in
      evar (g:t);
      erewrite (fold_left_ext f g) by derive_spec
    end
  end.

