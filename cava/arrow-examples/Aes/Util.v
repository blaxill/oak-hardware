
Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Arrow.

Require Import Cava.Arrow.Instances.Prop.

From Coq Require Import NArith.

Import KappaNotation.

Section var.

Variable var: Kind -> Kind -> Type.

Fixpoint reduce {n T}
  (f : kappa_sugared var <<T, T, Unit>> T)
  {struct n}
  : kappa_sugared var << Vector (S n) T, Unit >> <<T>> :=
match n with
| 0 => <[ \x => x[#0] ]>
| S n' => 
  <[ \xs =>
      let '(x, xs') = !(kappa_head') xs in
      let y = !(reduce f) xs' in
      !f x y 
  ]>
end.

Fixpoint map {n T}
  (f : kappa_sugared var <<T, Unit>> T)
  : kappa_sugared var << Vector (S n) T, Unit >> <<Vector (S n) T>> :=
match n with
| 0 => <[ \x => mkVec (!f (x[#0])) ]> 
| S n' =>
  <[ \xs =>
      let '(x, xs') = !kappa_head' xs in
      !f x :: (!(@map n' _ f) xs') 
  ]> 
end.

Fixpoint map2 {n T}
  (f : kappa_sugared var <<T, T, Unit>> T)
  : kappa_sugared var << Vector (S n) T, Vector (S n) T, Unit >> <<Vector (S n) T>> :=
match n with
| 0 => <[ \x y => mkVec (!f (x[#0]) (y[#0])) ]> 
| S n' =>
  <[ \xs ys =>
      let '(x, xs') = !kappa_head' xs in
      let '(y, ys') = !kappa_head' ys in
      !f x y :: (!(@map2 n' _ f) xs' ys') 
  ]> 
end.

Definition map2_xor {n}
  : kappa_sugared var << Vector (S n) Bit, Vector (S n) Bit, Unit >> <<Vector (S n) Bit>> :=
  map2 Xor.

Definition map2_xnor {n}
  : kappa_sugared var << Vector (S n) Bit, Vector (S n) Bit, Unit >> <<Vector (S n) Bit>> :=
  map2 Xnor.

Definition bitvec_eq {n}
  : kappa_sugared var << Vector (S n) Bit, Vector (S n) Bit, Unit >> <<Bit>> :=
  <[\ x y => !(reduce And) (!map2_xnor x y) ]>.

Definition enable_vec {n}
  : kappa_sugared var << Bit, Vector (S n) Bit, Unit >> <<Vector (S n) Bit>> :=
  <[\ enable xs => !(map (App And (Var enable))) xs ]>.

Definition mux_vec {n}
  : kappa_sugared var << Bit, Vector (S n) Bit, Vector (S n) Bit, Unit >> <<Vector (S n) Bit>> :=
  <[\ switch xs ys => 
    let not_switch = not switch
    in !(map2 Or) (!enable_vec switch xs) (!enable_vec not_switch ys)
    ]>.

End var.


Notation "a ^ b" := (App (App (map2_xor _) a) b) (in custom expr at level 5, left associativity) : kappa_scope.
Notation "a & b" := (App (App (map2 _ And) a) b) (in custom expr at level 5, left associativity) : kappa_scope.
Notation "a == b" := (App (App (bitvec_eq _) a) b) (in custom expr at level 5, left associativity) : kappa_scope.
Notation "'if' i 'then' t 'else' e" := (App (App (App (mux_vec _) i) t) e) (in custom expr at level 5, left associativity) : kappa_scope.