Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Arrow.

From Coq Require Import NArith Lia.

Import KappaNotation.

Require Import Util List.

Section var.
Variable var: Kind -> Kind -> Type.

(* // Multiplication in GF(2^2), using normal basis [Omega^2, Omega] *)
(* // (see Figure 14 in the technical report) *)
(* function automatic logic [1:0] aes_mul_gf2p2(logic [1:0] g, logic [1:0] d); *)
(*   logic [1:0] f; *)
(*   logic       a, b, c; *)
(*   a    = g[1] & d[1]; *)
(*   b    = (^g) & (^d); *)
(*   c    = g[0] & d[0]; *)
(*   f[1] = a ^ b; *)
(*   f[0] = c ^ b; *)
(*   return f; *)
(* endfunction *)
Definition aes_mul_gf2p2
  : kappa_sugared var << Vector 2 Bit , Vector 2 Bit , Unit >> << Vector 2 Bit>> :=
<[ \g d =>
  let a = and (g[#1]) (d[#1]) in
  let g_xor = !(reduce _ Xor) g in
  let d_xor = !(reduce _ Xor) d in
  let b = and g_xor d_xor in
  let c = and (g[#0]) (d[#0]) in
  mkVec
    ( xor c b
    , xor a b
    )
]>.

(* // Scale by Omega^2 = N in GF(2^2), using normal basis [Omega^2, Omega] *)
(* // (see Figure 16 in the technical report) *)
(* function automatic logic [1:0] aes_scale_omega2_gf2p2(logic [1:0] g); *)
(*   logic [1:0] d; *)
(*   d[1] = g[0]; *)
(*   d[0] = g[1] ^ g[0]; *)
(*   return d; *)
(* endfunction *)
Definition aes_scale_omega2_gf2p2
  : kappa_sugared var << Vector 2 Bit, Unit >> << Vector 2 Bit >> :=
<[ \g =>
  mkVec 
    ( xor (g[#1]) (g[#0])
    , g[#0]
    )
]>.

(* // Scale by Omega = N^2 in GF(2^2), using normal basis [Omega^2, Omega] *)
(* // (see Figure 15 in the technical report) *)
(* function automatic logic [1:0] aes_scale_omega_gf2p2(logic [1:0] g); *)
(*   logic [1:0] d; *)
(*   d[1] = g[1] ^ g[0]; *)
(*   d[0] = g[1]; *)
(*   return d; *)
(* endfunction *)
Definition aes_scale_omega_gf2p2
  : kappa_sugared var << Vector 2 Bit, Unit >> << Vector 2 Bit >> :=
<[ \g =>
  mkVec
    ( g[#1]
    , xor (g[#1]) (g[#0])
    )
]>.

(* // Square in GF(2^2), using normal basis [Omega^2, Omega] *)
(* // (see Figures 8 and 10 in the technical report) *)
(* function automatic logic [1:0] aes_square_gf2p2(logic [1:0] g); *)
(*   logic [1:0] d; *)
(*   d[1] = g[0]; *)
(*   d[0] = g[1]; *)
(*   return d; *)
(* endfunction *)
Definition aes_square_gf2p2
  : kappa_sugared var << Vector 2 Bit, Unit >> << Vector 2 Bit >> :=
<[ \g =>
  mkVec
    ( g[#1]
    , g[#0]
    )
]>.

(* // Multiplication in GF(2^4), using normal basis [alpha^8, alpha^2] *)
(* // (see Figure 13 in the technical report) *)
(* function automatic logic [3:0] aes_mul_gf2p4(logic [3:0] gamma, logic [3:0] delta); *)
(*   logic [3:0] theta; *)
(*   logic [1:0] a, b, c; *)
(*   a          = aes_mul_gf2p2(gamma[3:2], delta[3:2]); *)
(*   b          = aes_mul_gf2p2(gamma[3:2] ^ gamma[1:0], delta[3:2] ^ delta[1:0]); *)
(*   c          = aes_mul_gf2p2(gamma[1:0], delta[1:0]); *)
(*   theta[3:2] = a ^ aes_scale_omega2_gf2p2(b); *)
(*   theta[1:0] = c ^ aes_scale_omega2_gf2p2(b); *)
(*   return theta; *)
(* endfunction *)
Definition aes_mul_gf2p4
  : kappa_sugared var << Vector 4 Bit, Vector 4 Bit, Unit >> << Vector 4 Bit >>.
refine (
<[ \gamma delta =>
  let a = !aes_mul_gf2p2 (gamma[3:2]) (delta[3:2]) in
  let b = !aes_mul_gf2p2 (gamma[3:2] ^ gamma[1:0]) (delta[3:2] ^ delta[1:0]) in
  let c = !aes_mul_gf2p2 (gamma[1:0]) (delta[1:0]) in
  concat
    (c ^ !aes_scale_omega2_gf2p2 b)
    (a ^ !aes_scale_omega2_gf2p2 b)
]>); compute; auto.
Defined.

(* // Square and scale by nu in GF(2^4)/GF(2^2), using normal basis [alpha^8, alpha^2] *)
(* // (see Figure 19 as well as Appendix A of the technical report) *)
(* function automatic logic [3:0] aes_square_scale_gf2p4_gf2p2(logic [3:0] gamma); *)
(*   logic [3:0] delta; *)
(*   logic [1:0] a, b; *)
(*   a          = gamma[3:2] ^ gamma[1:0]; *)
(*   b          = aes_square_gf2p2(gamma[1:0]); *)
(*   delta[3:2] = aes_square_gf2p2(a); *)
(*   delta[1:0] = aes_scale_omega_gf2p2(b); *)
(*   return delta; *)
(* endfunction *)
Definition aes_square_scale_gf2p4_gf2p2
  : kappa_sugared var << Vector 4 Bit, Unit >> << Vector 4 Bit >>.
refine (
<[ \gamma =>
    let a = gamma[3:2] ^ gamma[1:0] in
    let b = !aes_square_gf2p2 (gamma[1:0]) in
    concat
      (!aes_scale_omega_gf2p2 b)
      (!aes_square_gf2p2 a)
]>); compute; auto.
Defined.

(* // Basis conversion matrices to convert between polynomial basis A, normal basis X *)
(* // and basis S incorporating the bit matrix of the SBox. More specifically, *)
(* // multiplication by X2X performs the transformation from normal basis X into *)
(* // polynomial basis A, followed by the affine transformation (substep 2). Likewise, *)
(* // multiplication by S2X performs the inverse affine transformation followed by the *)
(* // transformation from polynomial basis A to normal basis X. *)
(* // (see Appendix A of the technical report) *)
(* parameter logic [7:0] A2X [8] = '{8'h98, 8'hf3, 8'hf2, 8'h48, 8'h09, 8'h81, 8'ha9, 8'hff}; *)
(* parameter logic [7:0] X2A [8] = '{8'h64, 8'h78, 8'h6e, 8'h8c, 8'h68, 8'h29, 8'hde, 8'h60}; *)
(* parameter logic [7:0] X2S [8] = '{8'h58, 8'h2d, 8'h9e, 8'h0b, 8'hdc, 8'h04, 8'h03, 8'h24}; *)
(* parameter logic [7:0] S2X [8] = '{8'h8c, 8'h79, 8'h05, 8'heb, 8'h12, 8'h04, 8'h51, 8'h53}; *)

End var.

Section sanity_check.
  Lemma aes_mul_gf2p2_wf: wf_debrujin ENil (Desugar (aes_mul_gf2p2 ) _).
  Proof.
    wf_kappa_via_equiv; intros;

  repeat match goal with 
  | [ |- In _ _ ] => simpl; tauto
  | [ H: In _ nil |- _] => inversion H
  end.


    repeat match goal with 
    | [ |- kappa_equivalence _ _ _] => constructor;intros
    end; simpl; tauto.
    
    intros; simpl.
    inversion H.
  Qed.

  Definition aes_mul_gf2p2_structure
    := to_constructive (Desugar (@aes_mul_gf2p2)) aes_mul_gf2p2_wf.
  Compute aes_mul_gf2p2_structure.

  Definition aes_mul_gf2p4_structure: structure << Vector 4 Bit, Vector 4 Bit >> << Vector 4 Bit >>
    := to_constructive (Desugar (@aes_mul_gf2p4)) aes_mul_gf2p4_wf.

  Require Import Cava.Arrow.Instances.Prop.
  Goal structure << Vector 4 Bit, Vector 4 Bit >> (Vector 4 Bit).
    set (circuit := aes_mul_gf2p4).
    set (circuit_wf := aes_mul_gf2p4_wf).

    match goal with 
    | [ circuit := ?circuit_kappa : forall var, kappa_sugared var ?I ?O
      , circuit_wf: wf_debrujin ENil (Desugar (?circuit_kappa) natvar) |- _] =>
      let circuit_structure := fresh circuit "_structure" in
        pose (to_constructive (Desugar circuit_kappa) circuit_wf) as circuit_structure
    end.
    match goal with 
    | [ circuit_structure : structure ?I ?O |- _] =>
      let circuit_no_loops := fresh circuit_structure "_no_loops" in
        pose (toCava circuit_structure NoLoops) as circuit_no_loops
        (* compute in circuit_no_loops *)
    end.

    hnf in circuit_structure_no_loops.
    compute in circuit_structure_no_loops.
    inversion circuit_structure_no_loops.
    apply (modular_prop _ _ _ _ _ _ ) in circuit_structure_no_loops.

    apply circuit_structure.

    apply (to_constructive (Desugar circuit) circuit_wf).

(* Definition to_constructive {i o} (expr: Kappa i o) (wf: wf_debrujin ENil (expr _))
  : structure (remove_rightmost_unit i) o *)

      (* pose proof (to_constructive (Desugar H1) H2) as x;
      clear H1; clear H2 *)
  (* | [ H1: forall var, kappa_sugared var ?I ?O |- _ ] => idtac *)
  (* | [ H2: wf_debrujin ENil (Desugar (?X) natvar) |- _ ] => idtac *)
  (* | [ H2: wf_debrujin ENil (Desugar (?X) natvar) |- _ ] => 
    (* idtac  *)
    idtac "hello " X
    match X with
    |  => match
    end *)
  end.

  Show Proof.
    mk_constructive.
End sanity_check.