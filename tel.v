(*

      Télescopes généralisés.

(d'après la notion de télescope décrite dans l'article de N.G. De Bruijn
 "Telescoping mappings in typed lambda calculus", 
Information and Computation, vol 91, No 2, pp 189-204, avril 91).

Un télescope est une suite d'abstractions:
[x1:T1][x2:T2(x1)]...[xn:Tn(x1,...,xn-1)]
*)
Set Implicit Arguments.

(* Un type pour représenter les télescopes: *)

Inductive tel: Type :=
  | T0: tel
  | Tc: forall T:Type, (T ->tel) ->tel .

Definition monoide:tel := 
 (Tc (fun A:Type =>
 (Tc (fun plus:A->A->A =>
 (Tc (fun zero:A =>
 (Tc (fun plus_assoc:
           forall x y z:A, plus (plus x y) z = plus x (plus y z) =>
 (Tc (fun plus_zero: forall x:A, plus x zero = x 
            => T0)))))))))).
                
(* Ce type contient en fait plus que les télescopes de De Bruijn, 
 puisque si x:T et f:T -> tel, le telescope f(x) peut etre de longueur 
variable selon x. Benjamin Werner m'a fait remarquer que c'est un type isomorphe à celui des ensembles de Peter Aczel. Tant mieux!
Pour déstructurer un télescope: *)

Definition tel_fst(t:tel):Type:=
 match t with T0 => True | Tc T P => T end.

Definition tel_fun(t:tel):tel_fst t -> tel.
induction t. intros. exact T0. simpl. exact t. Defined.

(* Un élément d'un télescope [x1:T1][x2:T2(x1)]...[xn:Tn(x1,...,xn-1)] est une suite de variables
 x1,...,xn avec les types correspondants. *)

Inductive el_tel: tel ->Type :=
  |el_T0: (el_tel T0)
  |el_Tc: forall (T:Type) (x:T) (f:T -> tel),
            (el_tel (f x)) -> (el_tel (Tc f)) .

(* Fonctions de déstructuration de ces éléments. *)

Definition el_fst: (t:tel) (e:(el_tel t))(tel_fst t).
Intros t e; Try Assumption.
Case e; Simpl.
Exact I.
Intros T x f H'; Try Assumption.
Defined.

Lemma el_fst_prop:
  (T:Type) (f:T ->tel) (x:T) (y:(el_tel (f x)))<T> (el_fst (el_Tc y))==x.
Simpl; Auto with core.
Qed.

Definition el_rem: (t:tel) (e:(el_tel t))(el_tel (!tel_fun t (el_fst e))).
Intros t e.
Case e.
Simpl.
Exact el_T0.
Simpl.
Intros T x f H'; Try Assumption.
Defined.

Lemma el_rem_prop_type:
  (T:Type) (f:T ->tel) (x:T) (y:(el_tel (f x)))
  (el_tel (f x))==(el_tel (!tel_fun (Tc f) (el_fst (el_Tc y)))).
Simpl; Auto with core.
Qed.

Lemma el_rem_prop:
  (T:Type) (f:T ->tel) (x:T) (y:(el_tel (f x)))
  <(el_tel (!tel_fun (Tc f) (el_fst (el_Tc y))))> (el_rem (el_Tc y))==y.
Simpl; Auto with core.
Qed.

(*
Le n-ième type d'un télescope.
*)

Definition tel_nth: (t:tel) nat -> (el_tel t) ->Type.
Fix 2.
Intros t n e.
Case n.
Exact (tel_fst t).
Intros n0.
Exact (tel_nth (tel_fun (el_fst e)) n0 (el_rem e)).
Defined.

(*
Le nième élément d'un élément de télescope.
*)

Definition el_nth: (t:tel) (n:nat) (e:(el_tel t))(tel_nth n e).
Fix 2.
Intros t n e.
Case n.
Exact (el_fst e).
Intros n0.
Exact (el_nth (tel_fun (el_fst e)) n0 (el_rem e)).
Defined.
