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

From Arrow Require Import Category ClosureConversion.
From Cava Require Import Arrow.ArrowExport.

From Coq Require Import Strings.String Bvector List NArith Nat Lia Plus.
Import ListNotations.
Import EqNotations.

Import KappaNotation.
Local Open Scope string_scope.
Local Open Scope kind_scope.

(* *************************** *)
(* Rewrites *)

Definition rewrite_kind {x y} (H: x = y) (cava: Cava)
  : << x, Unit >> ~> y :=
  match decKind x y with
  | left Heq =>
    rew [fun x => << _ >> ~> <<x>> ] Heq in <[\x=>x]> cava
  | right Hneq => (ltac:(contradiction))
  end.

Definition rewrite_vector {A x y} (H: x = y) (cava: Cava)
  : << Vector A x, Unit >> ~> <<Vector A y>> :=
  match PeanoNat.Nat.eq_dec x y with
  | left Heq =>
    rew [fun x => << _, _ >> ~> <<Vector A x>> ] Heq in <[\x=>x]> cava
  | right Hneq => (ltac:(contradiction))
  end.

Definition split_pow2 A n
  : forall cava: Cava, << Vector A (2^(S n)), Unit >> ~> <<Vector A (2^n), Vector A (2^n)>>.
  refine (<[\ x => 
    let '(l,r) = split_at (2^n) x in
    (l, !(rewrite_vector _) r)
      ]>);
  induction n; simpl; auto; nia.
Defined.

(* *************************** *)
(* Tree folds, expecting a vector of input size pow2 *)

Fixpoint tree (A: Kind) (n: nat)
  (f: forall cava: Cava, << A, A, Unit >> ~> A) {struct n}
  : forall cava: Cava, << Vector A (2^n), Unit >> ~> A :=
match n with
| O => <[ \ vec => let '(x,_) = uncons vec in x ]>
| S n' => 
  <[\ x =>
      let '(left,right) = !(split_pow2 A n') x in
      let a = !(tree A n' f) left in
      let b = !(tree A n' f) right in
      !f a b
  ]>
end.

Fixpoint dt_tree_fold'
  (n k: nat)
  (T: nat -> Kind)
  (f: forall n, forall cava: Cava, << T n, T n, Unit >> ~> (T (S n))) {struct n}
  : forall cava: Cava, << Vector (T k) (2^n), Unit >> ~> (T (n + k)) :=
match n with
| O => <[ \ vec => let '(x,_) = uncons vec in x ]>
| S n' =>  
  <[\ x =>
      let '(left,right) = !(split_pow2 (T k) n') x in
      let a = !(dt_tree_fold' n' k T f) left in
      let b = !(dt_tree_fold' n' k T f) right in
      !(f _) a b
  ]>
end.

Lemma inj_succ_in_kind: forall n (T: nat -> Kind), T (n + 0) = T n.
Proof. auto. Qed.

Definition dt_tree_fold
  (n: nat)
  (T: nat -> Kind)
  (f: forall n, forall cava: Cava, << T n, T n, Unit >> ~> T (S n)) 
  : forall cava: Cava, << Vector (T 0) (2^n), Unit >> ~> T n :=
  <[ \vec => !(rewrite_kind (inj_succ_in_kind _ _)) (!(dt_tree_fold' n 0 T f) vec) ]>.

(* *************************** *)
(* element mapping *)

Fixpoint foldl {n A B}
  (f: forall cava: Cava, <<B, A, Unit>> ~> B)
  (initial: forall cava: Cava, <<Unit>> ~> B)
  {struct n}
  : forall cava: Cava, << Vector A n, Unit >> ~> <<B>> :=
match n with
| 0 => <[ \_ => !initial ]>
| S n' =>
  <[ \xs =>
      let '(x, xs') = uncons xs in
      let acc = !(foldl f initial) xs' in
      !f acc x
  ]>
end.

Fixpoint foldr {n A B}
  (f: forall cava: Cava, <<A, B, Unit>> ~> B)
  (initial: forall cava: Cava, <<Unit>> ~> B)
  {struct n}
  : forall cava: Cava, << Vector A n, Unit >> ~> <<B>> :=
match n with
| 0 => <[ \_ => !initial ]>
| S n' =>
  <[ \xs =>
      let '(xs', x) = unsnoc xs in
      let acc = !(foldr f initial) xs' in
      !f x acc
  ]>
end.

(* non-empty version, doesn't require a default *)
Fixpoint foldl1 {n T}
  (f: forall cava: Cava, <<T, T, Unit>> ~> T)
  {struct n}
  : forall cava: Cava, << Vector T (S n), Unit >> ~> <<T>> :=
match n with
| 0 => <[ \x => x[#0] ]>
| S n' =>
  <[ \xs =>
      let '(x, xs') = uncons xs in
      let acc = !(foldl1 f) xs' in
      !f acc x
  ]>
end.

Fixpoint map {n A B}
  (f : forall cava: Cava, <<A, Unit>> ~> B)
  : forall cava: Cava, << Vector A n, Unit >> ~> <<Vector B n>> :=
match n with
| 0 => <[ \x => [] ]>
| S n' =>
  <[ \xs =>
      let '(x, xs') = uncons xs in
      !f x :: (!(map f) xs')
  ]>
end.

Fixpoint map2 {n A B C}
  (f : forall cava: Cava, <<A, B, Unit>> ~> C)
  : forall cava: Cava, << Vector A n, Vector B n, Unit >> ~> <<Vector C n>> :=
match n with
| 0 => <[ \x y => [] ]>
| S n' =>
  <[ \xs ys =>
      let '(x, xs') = uncons xs in
      let '(y, ys') = uncons ys in
      !f x y :: (!(map2 f) xs' ys')
  ]>
end.

Fixpoint equality {T}
  : forall cava: Cava, << T, T, Unit >> ~> <<Bit>> :=
match T return forall cava: Cava, << T, T, Unit >> ~> <<Bit>> with 
| Unit => <[ \_ _ => true ]>
| Bit => <[ \x y => xnor x y ]> (* bit equality is the xnor function *)
| Tuple l r => <[ 
    \x y => 
      let '(a,b) = x in
      let '(c,d) = y in
      and (!equality a c) (!equality b d)
  ]>
| Vector ty n => 
  <[\ x y => 
    let item_equality = !(map2 equality) x y in
    !(foldl <[\x y => and x y]> <[ true ]>) item_equality
  ]>
end.

Fixpoint replicate {n T}
  : forall cava: Cava, <<T, Unit>> ~> Vector T n :=
match n with
| 0 => <[ \_ => [] ]>
| S n' =>
  <[ \x => x :: !(replicate (n:=n')) x ]>
end.

(* if the enable input is 1 then the vector is return as is,
otherwise a vector of corresponding size is returned with all elements masked out to 0. *)
Definition enable_vec {n}
  : forall cava: Cava, << Bit, Vector Bit n, Unit >> ~> <<Vector Bit n>> :=
  <[\ enable xs => !(map2 <[\x y => and x y]>) (!replicate enable) xs ]>.

Definition mux_bitvec {n}
  : forall cava: Cava, << Bit, Vector Bit n, Vector Bit n, Unit >> ~> <<Vector Bit n>> :=
  <[\ switch xs ys =>
      let not_switch = not switch
      in !(map2 <[\x y => or x y ]>) (!enable_vec switch xs) (!enable_vec not_switch ys)
  ]>.

(* *************************** *)
(* Combinators *)

Definition below {A B C D E F G: Kind}
  (r: forall cava: Cava, << A, B, Unit >> ~> << G, D >>)
  (s: forall cava: Cava, << G, C, Unit >> ~> << F, E >>)
  : forall cava: Cava,  
    << A, <<B, C>>, Unit >> ~> << F, <<D, E>> >> :=
<[ \ a bc =>
  let '(b, c) = bc in
  let '(g, d) = !r a b in
  let '(f, e) = !s g c in
  (f, (d, e))
]>.

(* Replicate a kind by a right imbalanced tupling of the kind *)
Fixpoint replicateKind A n : Kind :=
  match n with
  | O => Unit
  | S O => A
  | S n => <<A, replicateKind A n>>
  end.

Fixpoint col' {A B C: Kind} n
  (circuit: forall cava: Cava, << A, B, Unit >> ~> <<A, C>>)
  {struct n}: forall cava: Cava,
    << A, replicateKind B (S n), Unit >> ~>
    << A, replicateKind C (S n)>> :=
  match n with
  | O => <[ \a b => !circuit a b ]> 
  | S n' =>
    let column_below := (col' n' circuit) in
    below circuit column_below 
  end.

Lemma col_cons: forall {A B C}
  (circuit: forall cava, << A, B, Unit >> ~> <<A, C>>),
  forall n, col' (S n) circuit = below circuit (col' n circuit).
Proof. auto. Qed.

Fixpoint productToVec {n T}
  : forall cava: Cava, << replicateKind T (S n), Unit >> ~> << Vector T (S n) >> :=
  match n with
  | 0 => <[\ x => x :: [] ]> 
  | S n' => 
      <[\ xs => 
        let '(x, xs') = xs in 
        x :: !productToVec xs'
      ]>
  end.

Fixpoint vecToProduct {n T}
  : forall cava: Cava, << Vector T (S n), Unit >> ~> << replicateKind T (S n) >> :=
match n with
| 0 => <[\ xs => let '(x,_) = uncons xs in x ]> 
| S n' => 
    <[\ xs => 
      let '(x, xs') = uncons xs in 
      (x, !vecToProduct xs')
    ]>
end.

Fixpoint interleaveVectors n
  : forall cava: Cava,
    << Vector Bit (S n), Vector Bit (S n), Unit >> ~>
    << Vector <<Bit, Bit>> (S n) >> :=
match n with
| 0 => <[\ x y => (x[#0], y[#0]) :: [] ]> 
| S n => 
    <[\ xs ys => 
    let '(x, xs') = uncons xs in 
    let '(y, ys') = uncons ys in 
    (x, y) :: (!(interleaveVectors n) xs' ys')
  ]>
end.

Definition col {A B C: Kind} n
  (circuit: forall cava: Cava, << A, B, Unit >> ~> <<A, C>>)
  : forall cava: Cava,
    << A, Vector B (S n), Unit >> ~>
    << A, Vector C (S n)>> :=
  <[ \a b => 
    let prod_b = !vecToProduct b in
    let '(a, c) = !(col' n circuit) a prod_b in
    (a, !productToVec c)
  ]>.

Section regression_tests.
  Definition halfAdder
  : forall cava: Cava, << Bit, Bit, Unit >> ~> <<Bit, Bit>> :=
  <[ \ a b =>
    let part_sum = xor a b in
    let carry = and a b in
    (part_sum, carry)
  ]>.

  Definition fullAdder
  : forall cava: Cava, << Bit, << Bit, Bit >>, Unit >> ~> <<Bit, Bit>> :=
  <[ \ cin ab =>
    let '(a,b) = ab in
    let '(abl, abh) = !halfAdder a b in
    let '(abcl, abch) = !halfAdder abl cin in
    let cout = xor abh abch in
    (abcl, cout)
  ]>.

  Definition rippleCarryAdder' (width: nat)
    : forall cava: Cava, 
      << Bit, Vector <<Bit, Bit>> (S width), Unit >> ~>
      << Bit, Vector Bit (S width) >> :=
  <[ !(col width fullAdder) ]>.

  Definition rippleCarryAdder (width: nat)
    : forall cava: Cava, 
      << Bit, <<Vector Bit (S width), Vector Bit (S width)>>, Unit >> ~>
      << Bit, Vector Bit (S width) >> :=
  <[ \b xy =>
    let '(x,y) = xy in
    let merged = !(interleaveVectors _) x y in
    let '(carry, result) = !(rippleCarryAdder' _) b merged in
    (carry, result)
    ]>.
End regression_tests.
