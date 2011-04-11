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
  | el_T0: (el T0)
  | el_Tc: forall (T:Type) (x:T) (f:T -> tel),
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

Notation "|| x : T ; P" := (Tc (\x : T, P))(at level 200, x ident, right associativity).  
Notation "|| x : T" := (Tc (\x : T, T0))(at level 200, x ident, right associativity).  
Notation "|| '_' : T ; P" := (Tc (\_ : T, P))(at level 200, right associativity).  
Notation "|| '_' : T" := (Tc (\_ : T, T0))(at level 200, right associativity).

(* exemple avec les classes de types *)

Class Associative{A:Type}(f:A->A->A):Prop:=
  associative: \/ x y z : A, (f (f x y) z) = (f x (f y z)).

(* magma associatif *)

Definition tel_magmaa :=
  || A : Type;
  || plus : Addition A;
  || _ : Associative plus.

Class Magmaa:Type := magmaa: el tel_magmaa.

Definition carrier(m:Magmaa):Type :=
  Eval compute -[elr el1] in eln m 0.
Coercion carrier:Magmaa >-> Sortclass.
Instance magmaa_plus(m:Magmaa):Addition m:= eln m 1.
Instance magmaa_plus_assoc(m:Magmaa):Associative _+_:= eln m 2.

Lemma l1:\/m:Magmaa, \/x y z:m, (x+y)+z = x+(y+z).
(*Set Printing All.*)
intros. 
Time rewrite magmaa_plus_assoc. 
Time trivial.
Qed.

Fixpoint add_tel(t:tel): (el t -> tel) -> tel:=
   match t as t0 return (el t0 -> tel) -> tel with
     | T0 => \ft: el T0 -> tel, ft el_T0
     | Tc T f => \ft: el (Tc f) -> tel, 
         Tc (\x:T, 
                add_tel (\e: el (f x), ft (el_Tc x _ e)))
   end.

Fixpoint coerce_tel(t:tel):\/ft:el t -> tel, el (add_tel ft) -> el t:=
  match
    t as t1 return (\/ ft :el t1 -> tel, el (add_tel ft) -> el t1)
  with
    | T0 => \ ft : el T0 -> tel, (fun _ : el (add_tel ft) => el_T0)
    | Tc T t1 =>
      \ ft : el (Tc t1) -> tel,
      (\ e : el (add_tel ft),
        el_Tc (el1 e) t1
        (coerce_tel
          (\ e2 : el (t1 (el1 e)), ft (el_Tc (el1 e) t1 e2))
          (elr e)))
  end.

(* monoide *)

Definition tel_monoide_diff(m:Magmaa):=
    || zero:Zero m;
    || _ : \/x:m, 0+x = x;
    || _ : \/x:m, x+0 = x.
Definition tel_monoide := Eval compute -[addition zero] in
  add_tel tel_monoide_diff.

Print tel_monoide.

Class Monoide:Type :=  
  monoide: el tel_monoide.
Definition Monoide_Magmaa: Monoide -> Magmaa:=
  coerce_tel tel_monoide_diff.
Coercion Monoide_Magmaa: Monoide >-> Magmaa.
Definition monoide_plus_zero(m:Monoide):= eln m 5.
Instance monoide_zero(m:Monoide):Zero m:= eln m 3.

Lemma l2:\/m:Monoide, \/x:m, x+0 = x.
intros. 
Time rewrite (monoide_plus_zero m). 
trivial.
Qed.

Lemma l3:\/m:Monoide, \/x y z:m, (x+y)+z = x+(y+z).
intros. 
Time rewrite (plus_assoc m).
Time trivial. (*0.1s*)
(* avec:
Time rewrite (eln m 2). (*1s*)
Time trivial. (*16s*)
*)
Time Qed. 


(* exemple d'instance *)

Inductive Bool:Type:= true|false.
Definition plusb(a b:Bool):= if a then if b then false else true else b.
Lemma plusb_assoc:\/a b c, plusb (plusb a b) c = plusb a (plusb b c).
induction a;induction b; induction c; simpl; auto.
Qed.

Definition Bmagmaa: Magmaa:=
   @el_Tc Type Bool _
  (el_Tc plusb _
  (el_Tc plusb_assoc _
  el_T0)).
Print Bmagmaa.

Notation "\\ x ; e1" := (el_Tc x _ e1)(at level 200, right associativity).  
Notation "\\ x ; " := (el_Tc x _ el_T0)(at level 200, right associativity).  
Print Bmagmaa.

Instance Magmaa_Bool:Magmaa := Bmagmaa.

Goal  \/x y z:Bmagmaa, (x+y)+z = x+(y+z).
intros. 
rewrite (eln Bmagmaa 2).
trivial.
Qed.
