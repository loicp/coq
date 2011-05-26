(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Export Morphisms Setoid Bool.
Require Import ZArith.
Open Scope Z_scope.
Require Import Algebra_syntax3.
Require Export Ring3.
Require Import Ring3_polynom.
Require Import Ring3_initial.


Instance multiplication_phi_ring{R:Type}`{Ring R} : Multiplication  :=
  {multiplication x y := (gen_phiZ x) * y}.

Set Implicit Arguments.

(* Reification with Type Classes, inspired from B.Grégoire and A.Spiewack *)

Class is_in_list_at (R:Type) (t:R) (l:list R) (i:nat).
Instance  Ifind0 (R:Type) (t:R) l
 : is_in_list_at t (t::l) 0.
Instance  IfindS (R:Type) (t2 t1:R) l i 
 `{is_in_list_at R t1 l i} 
 : is_in_list_at t1 (t2::l) (S i) | 1.

Class reifyPE (R:Type) (e:PExpr Z) (lvar:list R) (t:R).

Instance  reify_plus (R:Type) `{Addition R}
  e1 lvar t1 e2 t2 
 `{reifyPE R e1 lvar t1} 
 `{reifyPE R e2 lvar t2} 
 : reifyPE (PEadd e1 e2) lvar (addition t1 t2).
Instance  reify_var (R:Type) t lvar i 
 `{is_in_list_at R t lvar i}
 : reifyPE (PEX Z (P_of_succ_nat i)) lvar t 
 | 100.

Class reifyPElist (R:Type) (lexpr:list (PExpr Z)) (lvar:list R) 
  (lterm:list R).
Instance reifyPE_nil (R:Type) lvar 
 : @reifyPElist R nil lvar (@nil R).
Instance reifyPE_cons (R:Type) e1 lvar t1 lexpr2 lterm2
 `{reifyPE R e1 lvar t1} `{reifyPElist R lexpr2 lvar lterm2} 
 : reifyPElist (e1::lexpr2) lvar (t1::lterm2).

Class is_closed_list T (l:list T).
Instance Iclosed_nil T 
 : is_closed_list (T:=T) nil.
Instance Iclosed_cons T t l 
 `{is_closed_list (T:=T) l} 
 : is_closed_list (T:=T) (t::l).

Definition list_reifyl (R:Type) lexpr lvar lterm 
 `{is_closed_list (T:=R) lvar}  `{reifyPElist R lexpr lvar lterm}
  := (lvar,lexpr).

Unset Implicit Arguments.

Lemma comm: forall (R:Type)`{Ring R}(c : Z) (x : R),
  x * (gen_phiZ c) == (gen_phiZ c) * x.
Admitted.
(*
induction c. intros. simpl. gen_rewrite. simpl. intros.
rewrite <- same_gen.
induction p. simpl.  gen_rewrite. rewrite IHp. reflexivity.
simpl.  gen_rewrite. rewrite IHp. reflexivity.
simpl.  gen_rewrite. 
simpl. intros. rewrite <- same_gen.
induction p. simpl. generalize IHp. clear IHp.
gen_rewrite. intro IHp.  rewrite IHp. reflexivity.
simpl. generalize IHp. clear IHp.
gen_rewrite. intro IHp.  rewrite IHp. reflexivity.
simpl.  gen_rewrite. Qed.
*)

(* Reification *)

Ltac lterm_goal g :=
  match g with

   ?t1 == ?t2 => constr:(t1::t2::nil)
  | ?t1 == ?t2 -> ?g => let lvar :=
    lterm_goal g in constr:(t1::t2::lvar)     
  end.

Ltac reify_goal lvar lexpr lterm:=
  (*idtac lvar; idtac lexpr; idtac lterm;*)
  match lexpr with
     nil => idtac
   | ?e::?lexpr1 =>  
        match lterm with
         ?t::?lterm1 => (*idtac "t="; idtac t; idtac e;*)
           let x := fresh "T" in
           set (x:= t);
           change x with 
             (@PEeval Z _ _ _ _ _ _ (@gen_phiZ _ _ _ _ _ _) N
                      (fun n:N => n) (@pow_N _ _ _)
                      lvar e); 
           clear x;
           reify_goal lvar lexpr1 lterm1
        end
  end.

(*Print HintDb typeclass_instances.*)

Lemma Zeqb_ok: forall x y : Z, Zeq_bool x y = true -> x == y.
 intros x y H. rewrite (Zeq_bool_eq x y H). reflexivity. Qed. 


 Ltac ring_gen :=
   match goal with
     |- ?g => let lterm := lterm_goal g in (* les variables *)
          idtac "terms:"; idtac lterm;
        match eval red in (list_reifyl (lterm:=lterm)) with
         | (?fv, ?lexpr) => 
          idtac "variables:";idtac fv;
           idtac "reifications:"; idtac lexpr;
           reify_goal fv lexpr lterm;
           match goal with 
             |- ?g => 
                apply (@ring_correct Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                       (@gen_phiZ_morph _ _ _ _ _ _ _ _ _)
                 (@comm _ _ _ _ _ _ _ _ _) Zeq_bool Zeqb_ok N (fun n:N => n)
                 (@pow_N _ _ _));
               [ apply mkpow_th; reflexivity
                 |vm_compute; reflexivity]
           end
       end
   end.

(* Pierre L: these tests should be done in a section, otherwise
   global axioms are generated. Ideally such tests should go in
   the test-suite directory *)
Section Tests.
 
Ltac ring3:= 
  intros;
  match goal with
    |- _ == _  =>
          ring_gen
  end.
Instance Zplusi:Addition Z:= Zplus.

Goal forall x y:Z, x + y == y + x.
intros. 
ring_gen.
match goal with
     |- ?g => let lterm := lterm_goal g in (* les variables *)
          idtac "terms:"; idtac lterm
end.
match eval red in (@list_reifyl Z _ _  (x + y :: x :: nil) _ _)
  with
         | (?fv, ?lexpr) => 
          idtac "variables:";idtac fv;
           idtac "reifications:"; idtac lexpr
 end.

ring_gen.
Admitted.
Context {R:Type}`{Ring R}.


Goal forall x y z:R, x == x .
ring3. 
Qed.

Goal forall x y z:R, x * y * z == x * (y * z).
ring3.
Qed.

Goal forall x y z:R, 3 * x * (2 * y * z) == 6 * (x * y) * z.
ring3.
Qed.

End Tests.