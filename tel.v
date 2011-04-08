(* Télescopes généralisés.
   Adapté de http://www-sop.inria.fr/croap/CFC/Tel/index.html *)

Set Implicit Arguments.

(* Syntaxe *)
Class Zero (A : Type) := zero : A.
Notation "0" := zero.
Class One (A : Type) := one : A.
Notation "1" := one.
Class Addition (A : Type) := addition : A -> A -> A.
Notation "_+_" := addition.
Notation "x + y" := (addition x y).
Class Multiplication {A B : Type} := multiplication : A -> B -> B.
Notation "_*_" := multiplication.
Notation "x * y" := (multiplication x y).
Class Subtraction (A : Type) := subtraction : A -> A -> A.
Notation "_-_" := subtraction.
Notation "x - y" := (subtraction x y).
Class Opposite (A : Type) := opposite : A -> A.
Notation "-_" := opposite.
Notation "- x" := (opposite(x)).
Class Equality {A : Type}:= equality : A -> A -> Prop.
Notation "_==_" := equality.
Notation "x == y" := (equality x y) (at level 70, no associativity).
Class Bracket (A B: Type):= bracket : A -> B.
Notation "[ x ]" := (bracket(x)).
Class Power {A B: Type} := power : A -> B -> A.
Notation "x ^ y" := (power x y).
Notation "\/ x y z ,  P" := (forall x y z, P)
   (at level 200, x ident, y ident, z ident).
Notation "\/ x y ,  P" := (forall x y, P)
   (at level 200, x ident, y ident).
Notation "\/ x , P" := (forall x, P)(at level 200, x ident).
Notation "\/ x y z : T ,  P" := (forall x y z : T, P)
   (at level 200, x ident, y ident, z ident).
Notation "\/ x y  : T ,  P" := (forall x y : T, P)
   (at level 200, x ident, y ident).
Notation "\/ x  : T , P" := (forall x : T, P)(at level 200, x ident).
Notation "\ x y z , P" := (fun x y z => P)
   (at level 200, x ident, y ident, z ident).
Notation "\ x y ,  P" := (fun x y => P)
   (at level 200, x ident, y ident).
Notation "\ x , P" := (fun x => P)(at level 200, x ident).
Notation "\ x y z : T , P" := (fun x y z : T => P)
   (at level 200, x ident, y ident, z ident).
Notation "\ x y : T ,  P" := (fun x y : T => P)
   (at level 200, x ident, y ident).
Notation "\ x : T , P" := (fun x : T => P)(at level 200, x ident).

(* Le type des téléscopes *)

Inductive tel: Type :=
  | T0: tel
  | Tc: forall T:Type, (T -> tel) -> tel .

Inductive el: tel ->Type :=
  |el_T0: (el T0)
  |el_Tc: forall (T:Type) (x:T) (f:T -> tel),
            (el (f x)) -> (el (Tc f)) .

Definition tel1(t:tel):=
  match t with
   | T0 => Prop
   | Tc T f => T
  end.

Definition el1(t:tel):el t -> tel1 t.
case t. intro. exact True.
simpl. intros T f e. inversion e. exact x.
Defined.

Definition telr(t:tel):el t -> tel:=
  match t as t0 return (el t0 -> tel) with
   | T0 => fun _ : el T0 => T0
   | Tc T f => \ e : el (Tc f), f (el1 e)
end.

Definition elr(t:tel)(e:el t): el (telr e).
elim e. simpl. exact el_T0. 
simpl. intros T x f e1. intro. exact e1. Defined.

(* Le n-ième type d'un télescope. *)

Fixpoint teln(t:tel)(e:el t)(n:nat){struct n}:Type:=
  match n with 
   | O => tel1 t
   | S n1 => teln (elr e) n1
 end.

Fixpoint eln(t:tel)(e:el t)(n:nat){struct n}:teln e n:=
  match n with 
   | O => el1 e
   | S n1 => eln (elr e) n1 
  end.

(* avec les classes de types *)

Class Magmaa:Type :=
  emagmaa:
  el (Tc (\A:Type,
     (Tc (\plus:Addition A,
     (Tc (\plus_assoc: \/x y z:A, (x + y) + z = x + (y + z),
     T0)))))).

Definition carrier(m:Magmaa):Type :=
  Eval compute -[elr el1] in eln m 0.
Coercion carrier:Magmaa >-> Sortclass.

Instance magmaa_plus(m:Magmaa):Addition m:= eln m 1.

Goal  \/m:Magmaa, \/x y z:m, (x+y)+z = x+(y+z).
intros. 
rewrite (eln m 2).
trivial.
Qed.

(* exemple *)

Inductive Bool:Type:= true|false.
Definition plusb(a b:Bool):= if a then if b then false else true else b.
Lemma plusb_assoc:\/a b c, plusb (plusb a b) c = plusb a (plusb b c).
induction a;induction b; induction c; simpl; auto.
Qed.

Definition Bmagmaa: el magmaa:=
  @el_Tc Type Bool _
  (el_Tc plusb _
  (el_Tc plusb_assoc _
  el_T0)).

Instance Magmaa_Bool:Magmaa := Bmagmaa.

