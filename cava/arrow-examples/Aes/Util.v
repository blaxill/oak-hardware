
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

Fixpoint map2_xor {n}
  : kappa_sugared var << Vector (S n) Bit, Vector (S n) Bit, Unit >> <<Vector (S n) Bit>> :=
match n with
| 0 => <[ \x y => mkVec (xor (x[#0]) (y[#0])) ]> 
| S n' =>
  <[ \xs ys =>
      let '(x, xs') = !kappa_head' xs in
      let '(y, ys') = !kappa_head' ys in
      concat
        (mkVec ( xor x y ))
        (!(@map2_xor n') xs' ys')
  ]> 
end.

End var.

Notation "a ^ b" := (App (App (map2_xor _) a) b) (in custom expr at level 5, left associativity) : kappa_scope.


(* Lemma reduce_wf: forall n i (f: Kappa_sugared <<i,i,Unit>> i), 
  wf_debrujin ENil (Desugar f _) ->
  wf_debrujin ENil (Desugar (fun var => @reduce var n _ (f _)) _).
Proof.
  induction n.

  intros.
  eapply (@kappa_wf _ _ nil%list).
  repeat (constructor;intros).
  simpl.
  tauto.

  intros.
  eapply (@kappa_wf _ _ nil%list).
  repeat (constructor;intros).

  eapply (@kappa_wf _ _ nil%list) in H.
  Qed. *)

Ltac mk_constructive := 
  match goal with 
  | [ H1: Kappa_sugared ?I ?O 
    , H2: wf_debrujin ENil ((Kappa_sugared ?I ?O) natvar)
        |- _] =>
      pose proof (to_constructive (Desugar H1) H2) as x;
      clear H1; clear H2
  end.

Ltac show_is_combinational x x_wf := 
  match goal with 
  | [H: structure ?I ?O |- _] => 
    let no_loops_x := fresh "no_loops" in (
      pose proof (toCava H NoLoops) as no_loops_x;
      let no_delays_x := fresh "no_delays" in (
        pose proof (toCava H NoDelays) as no_delays_x
      )
    )
  end.