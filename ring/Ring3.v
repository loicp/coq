(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* non commutative rings *)

Require Import Setoid.
Require Import BinPos.
Require Import BinNat.
Require Export Morphisms Setoid Bool.
Require Export ZArith.
Require Export Algebra_syntax3.

Set Implicit Arguments.

Class Ring (R:Type)`{Zero R}`{One R}`{Addition R}
  `{Multiplication R R}`{Subtraction R}
  `{Opposite R}`{Equality R}:={
 ring_setoid: Equivalence _==_;
 ring_plus_comp: Proper (_==_ ==> _==_ ==>_==_) _+_;
 ring_mult_comp: Proper (_==_ ==> _==_ ==>_==_) _*_;
 ring_sub_comp: Proper (_==_ ==> _==_ ==>_==_) _-_;
 ring_opp_comp: Proper (_==_==>_==_) -_;
 ring_add_0_l    : \/x, 0 + x == x;
 ring_add_comm   : \/x y, x + y == y + x;
 ring_add_assoc  : \/x y z, x + (y + z) == (x + y) + z;
 ring_mul_1_l    : \/x, 1 * x == x;
 ring_mul_1_r    : \/x, x * 1 == x;
 ring_mul_assoc  : \/x y z, x * (y * z) == (x * y) * z;
 ring_distr_l    : \/x y z, (x + y) * z == x * z + y * z;
 ring_distr_r    : \/x y z, z * ( x + y) == z * x + z * y;
 ring_sub_def    : \/x y, x - y == x + -y;
 ring_opp_def    : \/x, x + -x == 0
}.

Existing Instance ring_setoid.
Existing Instance ring_plus_comp.
Existing Instance ring_mult_comp.
Existing Instance ring_sub_comp.
Existing Instance ring_opp_comp.

Section Ring_power.

Context {R:Type}`{Ring R}.

 Fixpoint pow_pos (x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow_pos x i in p * p
  | xI i => let p := pow_pos x i in x * (p * p)
  end.

 Definition pow_N (x:R) (p:N) :=
  match p with
  | N0 => 1
  | Npos p => pow_pos x p
  end.

End Ring_power.

Definition ZN(x:Z):=
  match x with
    Z0 => N0
    |Zpos p | Zneg p => Npos p
end.

Instance power_ring {R:Type}`{Rr:Ring} : Power:=
  \x, \y, pow_N x (ZN y).

(** Interpretation morphisms definition*)

Class Ring_morphism (C R:Type)`{Ring C} `{Ring R}:= {
    ring_morphism_fun: C -> R;
    ring_morphism0    : ring_morphism_fun 0 == 0;
    ring_morphism1    : ring_morphism_fun 1 == 1;
    ring_morphism_add : \/x y, ring_morphism_fun (x + y)
                     == ring_morphism_fun x + ring_morphism_fun y;
    ring_morphism_sub : \/x y, ring_morphism_fun (x - y)
                     == ring_morphism_fun x - ring_morphism_fun y;
    ring_morphism_mul : \/x y, ring_morphism_fun (x * y)
                     == ring_morphism_fun x * ring_morphism_fun y;
    ring_morphism_opp : \/ x, ring_morphism_fun (-x)
                          == -(ring_morphism_fun x);
    ring_morphism_eq  : \/x y, x == y
       -> ring_morphism_fun x == ring_morphism_fun y}.

Instance bracket_ring `{Ring_morphism}: Bracket C R :=
  ring_morphism_fun.

Section Ring.

Context {R:Type}`{Ring R}.

(* Powers *)

 Lemma pow_pos_comm : \/ x j,  x * pow_pos x j == pow_pos x j * x.
induction j; simpl. rewrite <- ring_mul_assoc.
rewrite <- ring_mul_assoc. 
rewrite <- IHj. rewrite (ring_mul_assoc (pow_pos x j) x (pow_pos x j)).
rewrite <- IHj. rewrite <- ring_mul_assoc. reflexivity.
rewrite <- ring_mul_assoc. rewrite <- IHj.
rewrite ring_mul_assoc. rewrite IHj.
rewrite <- ring_mul_assoc. rewrite IHj. reflexivity. reflexivity.
Qed.

 Lemma pow_pos_Psucc : \/ x j, pow_pos x (Psucc j) == x * pow_pos x j.
 Proof.
  induction j; simpl. 
  rewrite IHj. 
rewrite <- (ring_mul_assoc x (pow_pos x j) (x * pow_pos x j)).
rewrite (ring_mul_assoc (pow_pos x j) x  (pow_pos x j)).
  rewrite <- pow_pos_comm.
rewrite <- ring_mul_assoc. reflexivity.
reflexivity. reflexivity.
Qed.

 Lemma pow_pos_Pplus : \/ x i j,
   pow_pos x (i + j) == pow_pos x i * pow_pos x j.
 Proof.
  intro x;induction i;intros.
  rewrite xI_succ_xO;rewrite Pplus_one_succ_r.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;
  rewrite pow_pos_Psucc.
  simpl;repeat rewrite ring_mul_assoc. reflexivity.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi. rewrite ring_mul_assoc. reflexivity.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite pow_pos_Psucc.
   simpl. reflexivity. 
 Qed.

 Definition id_phi_N (x:N) : N := x.

 Lemma pow_N_pow_N : \/ x n, pow_N x (id_phi_N n) == pow_N x n.
 Proof.
  intros; reflexivity.
 Qed.

 (** Identity is a morphism *)
 
 Instance IDmorph : Ring_morphism.
 Proof.
  apply (Build_Ring_morphism H6 H6 (fun x => x));intros;
  try reflexivity. trivial.
 Qed.

 (** rings are almost rings*)
 Lemma ring_mul_0_l : \/ x, 0 * x == 0.
 Proof.
  intro x. setoid_replace (0*x) with ((0+1)*x + -x). 
  rewrite ring_add_0_l. rewrite ring_mul_1_l .
  rewrite ring_opp_def . fold zero. reflexivity.
  rewrite ring_distr_l . rewrite ring_mul_1_l .
  rewrite <- ring_add_assoc ; rewrite ring_opp_def .
  rewrite ring_add_comm ; rewrite ring_add_0_l ;reflexivity.
 Qed.

 Lemma ring_mul_0_r : \/ x, x * 0 == 0.
 Proof.
  intro x; setoid_replace (x*0)  with (x*(0+1) + -x).
  rewrite ring_add_0_l ; rewrite ring_mul_1_r .
  rewrite ring_opp_def ; fold zero; reflexivity.

  rewrite ring_distr_r ;rewrite ring_mul_1_r .
  rewrite <- ring_add_assoc ; rewrite ring_opp_def .
  rewrite ring_add_comm ; rewrite ring_add_0_l ;reflexivity.
 Qed.

 Lemma ring_opp_mul_l : \/x y, -(x * y) == -x * y.
 Proof.
  intros x y;rewrite <- (ring_add_0_l (- x * y)).
  rewrite ring_add_comm .
  rewrite <- (ring_opp_def (x*y)).
  rewrite ring_add_assoc .
  rewrite <- ring_distr_l.
  rewrite (ring_add_comm (-x));rewrite ring_opp_def .
  rewrite ring_mul_0_l;rewrite ring_add_0_l ;reflexivity.
 Qed.

Lemma ring_opp_mul_r : \/x y, -(x * y) == x * -y.
 Proof.
  intros x y;rewrite <- (ring_add_0_l (x * - y)).
  rewrite ring_add_comm .
  rewrite <- (ring_opp_def (x*y)).
  rewrite ring_add_assoc .
  rewrite <- ring_distr_r .
  rewrite (ring_add_comm (-y));rewrite ring_opp_def .
  rewrite ring_mul_0_r;rewrite ring_add_0_l ;reflexivity.
 Qed.

 Lemma ring_opp_add : \/x y, -(x + y) == -x + -y.
 Proof.
  intros x y;rewrite <- (ring_add_0_l  (-(x+y))).
  rewrite <- (ring_opp_def  x).
  rewrite <- (ring_add_0_l  (x + - x + - (x + y))).
  rewrite <- (ring_opp_def  y).
  rewrite (ring_add_comm  x).
  rewrite (ring_add_comm  y).
  rewrite <- (ring_add_assoc  (-y)).
  rewrite <- (ring_add_assoc  (- x)).
  rewrite (ring_add_assoc   y).
  rewrite (ring_add_comm  y).
  rewrite <- (ring_add_assoc   (- x)).
  rewrite (ring_add_assoc  y).
  rewrite (ring_add_comm  y);rewrite ring_opp_def .
  rewrite (ring_add_comm  (-x) 0);rewrite ring_add_0_l .
  rewrite ring_add_comm; reflexivity.
 Qed.

 Lemma ring_opp_opp : \/ x, - -x == x.
 Proof.
  intros x; rewrite <- (ring_add_0_l (- -x)).
  rewrite <- (ring_opp_def x).
  rewrite <- ring_add_assoc ; rewrite ring_opp_def .
  rewrite (ring_add_comm  x); rewrite ring_add_0_l . reflexivity.
 Qed.

 Lemma ring_sub_ext :
      \/ x1 x2, x1 == x2 -> \/ y1 y2, y1 == y2 -> x1 - y1 == x2 - y2.
 Proof.
  intros.
  setoid_replace (x1 - y1)  with (x1 + -y1).
  setoid_replace (x2 - y2)  with (x2 + -y2).
  rewrite H7;rewrite H8;reflexivity.
  rewrite ring_sub_def. reflexivity.
  rewrite ring_sub_def. reflexivity.
 Qed.

 Ltac mrewrite :=
   repeat first
     [ rewrite ring_add_0_l
     | rewrite <- (ring_add_comm 0)
     | rewrite ring_mul_1_l
     | rewrite ring_mul_0_l
     | rewrite ring_distr_l
     | reflexivity
     ].

 Lemma ring_add_0_r : \/ x, (x + 0) == x.
 Proof. intros; mrewrite. Qed.

 
 Lemma ring_add_assoc1 : \/x y z, (x + y) + z == (y + z) + x.
 Proof.
  intros;rewrite <- (ring_add_assoc x).
  rewrite (ring_add_comm x);reflexivity.
 Qed.

 Lemma ring_add_assoc2 : \/x y z, (y + x) + z == (y + z) + x.
 Proof.
  intros; repeat rewrite <- ring_add_assoc.
   rewrite (ring_add_comm x); reflexivity.
 Qed.

 Lemma ring_opp_zero : -0 == 0.
 Proof.
  rewrite <- (ring_mul_0_r 0). rewrite ring_opp_mul_l.
  repeat rewrite ring_mul_0_r. reflexivity.
 Qed.

End Ring.

(** Some simplification tactics*)
Ltac gen_reflexivity := reflexivity.
 
Ltac gen_rewrite :=
  repeat first
     [ reflexivity
     | progress rewrite ring_opp_zero
     | rewrite ring_add_0_l
     | rewrite ring_add_0_r
     | rewrite ring_mul_1_l 
     | rewrite ring_mul_1_r
     | rewrite ring_mul_0_l 
     | rewrite ring_mul_0_r 
     | rewrite ring_distr_l 
     | rewrite ring_distr_r 
     | rewrite ring_add_assoc 
     | rewrite ring_mul_assoc
     | progress rewrite ring_opp_add 
     | progress rewrite ring_sub_def 
     | progress rewrite <- ring_opp_mul_l 
     | progress rewrite <- ring_opp_mul_r ].

Ltac gen_add_push x :=
repeat (match goal with
  | |- context [(?y + x) + ?z] =>
     progress rewrite (@ring_add_assoc2 _ _ x y z)
  | |- context [(x + ?y) + ?z] =>
     progress rewrite  (@ring_add_assoc1 _ _ x y z)
  end).
