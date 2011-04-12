(* Télescopes généralisés.
   Adapté de http://www-sop.inria.fr/croap/CFC/Tel/index.html *)

Set Implicit Arguments.

(****************************** Syntaxe *)

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

(****************************** Le type des téléscopes *)

Inductive tel: Type :=
  | T0: tel
  | Tc: forall T:Type, (T -> tel) -> tel .

Inductive el: tel ->Type :=
  | el_T0: (el T0)
  | el_Tc: forall (T:Type) (x:T) (f:T -> tel),
            (el (f x)) -> (el (Tc f)) .
Set Printing All.
Set Printing Universes.

Definition t1:= Tc (\A:Type, T0).
Print t1.
Check (el t1).
Check t1.
Check (\B:el t1, T0).
Check Tc (\B:el t1, T0).
(*
el t1
     : Type (* max(Set, (Top.6)+1, (Top.2)+1) *)
t1 = @Tc Type (* Top.298 *) (fun _ : Type (* Top.297 *) => T0)
     : tel
*)
Definition t2:= Tc (\B:el t1, T0). (*Error: Universe inconsistency.*)

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

Notation "|| x : T ; P" := (Tc (\x : T, P))(at level 200, x ident, right associativity).  
Notation "|| x : T" := (Tc (\x : T, T0))(at level 200, x ident, right associativity).  
Notation "|| '_' : T ; P" := (Tc (\_ : T, P))(at level 200, right associativity).  
Notation "|| '_' : T" := (Tc (\_ : T, T0))(at level 200, right associativity).

(****************************** exemples *)

Class Zero (A : Type) := zero : A.
Notation "0" := zero.
Class Law(A:Type):= law:A->A->A.
Class Addition (A : Type) := addition : Law A.
Notation "_+_" := addition.
Notation "x + y" := (addition x y).
Class PROP:=prop:Prop.

Class Relation(A:Type):Type:= relation:A->A->PROP.
Class Equality (A : Type):= equality : Relation A.
Notation "_==_" := equality.
Notation "x == y" := (equality x y) (at level 70, no associativity).

Class Conjonction(A:Type):= conjonction:Law A.
Notation "x 'et' y" := (conjonction x y) (at level 80).

(****************************** relations *)

Class Reflexive{A:Type}(R:Relation A):PROP:= reflexive:\/x, R x x.
Class Symetrique{A:Type}(R:Relation A):PROP:= symetrique:\/x y, R x y -> R y x.
Instance conj_prop:Conjonction PROP:= and.
Class Transitive{A:Type}(R:Relation A):PROP:=
  transitive:\/x y z, R x y et R y z -> R x z.

Section equivalences.
Context {A:Type}{R:Relation A}.

Definition tel_equivalence:=
  || _:Reflexive R;
  || _:Symetrique R;
  || _:Transitive R.

Class Equivalence:= equivalence: el tel_equivalence.

Instance equivalence_reflexive(m:Equivalence):Reflexive R := eln m 0.
Instance equivalence_symetrique(m:Equivalence):Symetrique R:= eln m 1.
Instance equivalence_transitive(m:Equivalence):Transitive R := eln m 2.
 
End equivalences.
(****************************** graphes *)
Definition tel_graphe:=
  || A:Type;
  || R:Relation A.

Class Graphe:Type := graphe: el tel_graphe.
Definition carrier(m:Graphe):Type :=
  Eval compute -[elr el1] in eln m 0.
Coercion carrier:Graphe >-> Sortclass.
Instance graphe_relation(m:Graphe):Relation m := eln m 1.

(****************************** setoide *)
Definition tel_setoide_diff(m:Graphe):= 
   || _:@Equivalence _ (@graphe_relation m).
(*Error: Universe inconsistency.*)

Definition tel_setoide := 
  Eval compute -[PROP Relation 
                 conjonction Reflexive Symetrique Transitive] in
  add_tel tel_setoide_diff.
Set Printing All.

Print tel_setoide.

Class Setoide:= setoide: el tel_setoide.
Definition Setoide_Graphe: Setoide -> Graphe:=
  coerce_tel tel_setoide_diff.
Coercion Setoide_Graphe: Setoide >-> Graphe.
Instance setoide_equality(E:Setoide):Equality E:= graphe_relation E.

Instance setoide_equivalence(E:Setoide):Equivalence (R:=_==_) :=
      (el_Tc (eln E 2) _
      (el_Tc (eln E 3) _
      (el_Tc (eln E 4) _
        el_T0))).
Print setoide_equivalence.
@equivalence_reflexive
Lemma l0:\/E:Setoide, \/x:E, x == x.
intros. apply equivalence_reflexive. apply setoide_equivalence.
Qed.
Lemma l1:\/E:Setoide, \/x y:E, x == y -> y == x.
intros. apply equivalence_symetrique. apply setoide_equivalence. trivial.
Qed.

(****************************** magma associatif *)

Class Associative{A:Setoide}(f:Law A):PROP:=
  associative: \/ x y z : A, (f (f x y) z) == (f x (f y z)).

Definition tel_magmaa_diff(A:Setoide):=
  || op : Law A;
  || _ : Associative op.

Definition tel_magmaa := 
  Eval compute -[PROP tel_equivalence Associative Relation  Law
    conjonction Reflexive Symetrique Transitive addition] in
  add_tel tel_magmaa_diff.
Set Printing All.
Print tel_magmaa.

Class Magmaa:Type := magmaa: el tel_magmaa.
Definition Magmaa_Setoide: Magmaa -> Setoide:=
  coerce_tel tel_magmaa_diff.
Coercion Magmaa_Setoide: Magmaa >-> Setoide.
Definition magmaa_law(m:Magmaa):Law m:= 
 (*Eval compute -[PROP Associative Relation  Law conjonction Reflexive Symetrique Transitive addition] in*)
   eln m 5.
Time Instance magmaa_law_assoc(m:Magmaa):Associative (@magmaa_law m):= eln m 6.


Lemma l2:\/m:Magmaa, \/x y z:m, (x+y)+z = x+(y+z).
intros. 
Time rewrite magmaa_law_assoc. 
Time trivial.
Qed.

(****************************** monoide *)

Class Neutre_a_droite{A:Setoide}(f:A->A->A)(e:A):PROP:=
  neutre_a_droite: \/x:A, (f x e) == x.

Definition tel_monoide_diff(m:Magmaa):=
    || zero:Zero m;
    || _ : \/x:m, 0+x == x;
    || _ : \/x:m, x+0 == x.
Definition tel_monoide := Eval compute -[addition zero] in
  add_tel tel_monoide_diff.

Print tel_monoide.

Class Monoide:Type :=  
  monoide: el tel_monoide.
Definition Monoide_Magmaa: Monoide -> Magmaa:=
  coerce_tel tel_monoide_diff.
Coercion Monoide_Magmaa: Monoide >-> Magmaa.
Instance monoide_zero(m:Monoide):Zero m:= eln m 7.
Definition monoide_plus_zero(m:Monoide):= eln m 9.

Lemma l3:\/m:Monoide, \/x:m, x+0 == x.
intros. 
Time apply (monoide_plus_zero m). 
trivial.
Qed.

Lemma l3:\/m:Monoide, \/x y z:m, (x+y)+z = x+(y+z).
intros. 
Time rewrite magmaa_plus_assoc.
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
rewrite magmaa_plus_assoc.
trivial.
Qed.
