(* Télescopes généralisés.
   Adapté de http://www-sop.inria.fr/croap/CFC/Tel/index.html *)

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

Set Implicit Arguments.

(****************************** Le type des téléscopes *)

Inductive tel:Type:=
  | T0:tel
  | Tc: \/T:Type,(T -> tel) -> tel.

Inductive Pt:Type:= pt:Pt.

(* éléments d'un téléscope *)

Class Pair{A:Type}(f:A->Type):= pair {pairx:A; pairfx:f pairx}.

Fixpoint el(t:tel):Type:=
  match t with
    | T0 => Pt
    | Tc T f => Pair (\x:T, el (f x))
  end.

(****************************** décomposition *)
Definition tel1(t:tel):=
  match t with
   | T0 => Prop
   | Tc T f => T
  end.

Definition el1{t:tel}:el t -> tel1 t.
case t. intro. exact True.
simpl. intros T f e. exact pairx.
Defined.

Definition telr{t:tel}:el t -> tel:=
  match t as t0 return (el t0 -> tel) with
   | T0 => fun _ : el T0 => T0
   | Tc T f => \ e, f (el1 e)
end.
 
Definition elr{t:tel}:\/e:el t, el (telr e):=
  match t as t0 return (\/ e0 :el t0, el (telr e0)) with
    | T0 => fun _ : el T0 => pt
    | Tc T t0 => \ e0 : el (Tc t0), (@pairfx _ _ e0)
  end.
 
Fixpoint teln{t:tel}(e:el t)(n:nat){struct n}:Type:=
  match n with 
   | O => tel1 t
   | S n1 => teln (elr e) n1
 end.

Fixpoint eln{t:tel}(e:el t)(n:nat){struct n}:teln e n:=
  match n with 
   | O => el1 e
   | S n1 => eln (elr e) n1
 end.

Notation "|| x : T ; P" := (Tc (\x : T, P))(at level 200, x ident, right associativity).  
Notation "|| x : T" := (Tc (\x : T, T0))(at level 200, x ident, right associativity).  
Notation "|| '_' : T ; P" := (Tc (\_ : T, P))(at level 200, right associativity).  
Notation "|| '_' : T" := (Tc (\_ : T, T0))(at level 200, right associativity).

Notation "\\ a ; b" :=  (pair _ a b)(at level 200, right associativity). 
Notation "\\ a " :=  (pair _ a pt)(at level 200, right associativity). 

(****************************** exemples *)

Class Neutre (A : Type) := neutre : A.
Class Loi(A:Type):= loi:A->A->A.
Class PROP:=prop:Prop.
Class Relation(A:Type):Type:= relation:A->A->PROP.
Class Equality (A : Type):= equality : Relation A.
Notation "_==_" := equality.
Notation "x == y" := (equality x y) (at level 70, no associativity).

Class Conjonction(A:Type):= conjonction:Loi A.
Notation "x 'et' y" := (conjonction x y) (at level 80).


(****************************** graphes *)
Definition tel_graphe:tel:= 
  || A:Type;
  || R:Relation A.

Set Printing All.
Print tel_graphe.
Unset Printing All.

Class Graphe:Type := graphe: el tel_graphe.
Definition carrier(m:Graphe):Type :=
  Eval compute -[elr el1] in @eln tel_graphe m 0.
Coercion carrier:Graphe >-> Sortclass.
Instance graphe_relation(m:Graphe):Relation m := @eln tel_graphe m 1.

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

Set Printing All.
Print tel_equivalence.
Unset Printing All.

Class Equivalence:= equivalence: el tel_equivalence.

Instance equivalence_reflexive(m:Equivalence):Reflexive R := @eln tel_equivalence m 0.
Instance equivalence_symetrique(m:Equivalence):Symetrique R:= @eln tel_equivalence m 1.
Instance equivalence_transitive(m:Equivalence):Transitive R := @eln tel_equivalence m 2.
 
End equivalences.

(****************************** setoide *)
Definition tel_setoide:=
  || m:Graphe;
  || _:@Equivalence _ (@graphe_relation m).
(* ya plus d'inconsistence d'univers :-) *)

Class Setoide:= setoide: el tel_setoide.
Instance Setoide_Graphe(E:Setoide):Graphe:=
  @eln tel_setoide E 0.
Coercion Setoide_Graphe: Setoide >-> Graphe.
Instance setoide_equality(E:Setoide):Equality E:= graphe_relation E.
Time Instance setoide_equivalence(E:Setoide):Equivalence (R:=_==_) :=
  @eln tel_setoide E 1.

Lemma l0:\/E:Setoide, \/x:E, x == x.
intros. apply (equivalence_reflexive (setoide_equivalence E)).
Qed.
Lemma l1:\/E:Setoide, \/x y:E, x == y -> y == x.
intros. apply (equivalence_symetrique (setoide_equivalence E)). trivial.
Qed.

(****************************** magma *)
Section Magma.

Class Compatible2{A:Setoide}(f:Loi A):PROP:=
  compatible2: \/ x x1:A, \/ y y1:A, x == x1 et y == y1 -> f x y == f x1 y1.

Definition tel_magma:=
  || A : Setoide;
  || op : Loi A;
  || _ : Compatible2 op.

Class Magma:Type := magma: el tel_magma.
Global Instance Magma_Setoide(m:Magma):Setoide:=
  @eln tel_magma m 0.
Coercion Magma_Setoide: Magma >-> Setoide.
Time Definition magma_loi(m:Magma):Loi m:= @eln tel_magma m 1. 
Time Definition magma_loi_compatible(m:Magma):Compatible2 (@magma_loi m):=
  @eln tel_magma m 2. 
Global Instance magma_loi_i(m:Magma):Loi m:= magma_loi m.

End Magma.

(****************************** commutatif *)
Section Magma_commutatif.
Notation "x + y" := (loi x y).

Class Commutative`{A:Magma}:PROP:=
  associative: \/ x y: A, x + y == y + x.

Definition tel_magma_commutatif:=
  || A : Magma;
  || _ : Commutative.

Class Magma_commutatif:Type := magma_commutatif: el tel_magma_commutatif.
Global Instance Magma_commutatif_Magma(m:Magma_commutatif):Magma:=
  @eln tel_magma_commutatif m 0.
Coercion Magma_commutatif_Magma: Magma_commutatif >-> Magma.

Time Definition magma_commutatif_loi(m:Magma_commutatif):Commutative:=
  @eln tel_magma_commutatif m 1. 

Lemma l2:\/m:Magma_commutatif, \/x y:m, x + y == y + x.
intros. 
Time apply magma_commutatif_loi.
Qed.
End Magma_commutatif.

(****************************** magma associatif *)

Section Magma_associatif.
Notation "x + y" := (loi x y).

Class Associative`{A:Magma}:PROP:=
  associative: \/ x y z : A, (loi (loi x y) z) == (loi x (loi y z)).

Definition tel_magma_associatif:=
  || A : Magma;
  || _ : Associative.

Class Magma_associatif:Type := magma_associatif: el tel_magma_associatif.
Global Instance Magma_associatif_Magma(m:Magma_associatif):Magma:=
  @eln tel_magma_associatif m 0.
Coercion Magma_associatif_Magma: Magma_associatif >-> Magma.

Time Definition magma_associatif_loi(m:Magma_associatif):Associative:=
  @eln tel_magma_associatif m 1. 

Lemma l2:\/m:Magma_associatif, \/x y z:m, (x+y)+z == x+(y+z).
intros. 
Time apply magma_associatif_loi. 
Qed.
End Magma_associatif.

(****************************** monoide *)
Section Monoide.
Notation "x + y" := (loi x y).

Class Neutre_a_droite{A:Magma_associatif}(e:A):PROP:=
  neutre_a_droite: \/x:A, x + e == x.
Class Neutre_a_gauche{A:Magma_associatif}(e:A):PROP:=
  neutre_a_gauche: \/x:A, e + x == x.

Definition tel_monoide:=
    || m:Magma_associatif;
    || e:Neutre m;
    || _:Neutre_a_droite e;
    || _:Neutre_a_gauche e.

Class Monoide:Type := monoide: el tel_monoide.
Global Instance Monoide_Magma_associatif(m:Monoide): Magma_associatif:=
  @eln tel_monoide m 0.
Coercion Monoide_Magma_associatif: Monoide >-> Magma_associatif.
Global Instance monoide_neutre(m:Monoide):Neutre m:= @eln tel_monoide m 1.
Definition monoide_neutre_a_gauche(m:Monoide):=  @eln tel_monoide m 3.
Definition monoide_neutre_a_droite(m:Monoide):=  @eln tel_monoide m 2.

Global Instance monoide_neutre_i(m:Monoide):Neutre m:= monoide_neutre m.

Notation "0" := neutre.

Lemma l3:\/m:Monoide, \/x:m, x+0 == x.
intros. 
Time apply monoide_neutre_a_droite.
Qed.

Lemma l4:\/m:Monoide, \/x y z:m, (x+y)+z == x+(y+z).
intros. 
Time apply magma_associatif_loi_assoc.
Time Qed. 

End Monoide.

(****************************** groupe *)
Section Groupe.
Notation "x + y" := (loi x y).
Notation "0" := neutre.

Class Inverse_a_droite{A:Monoide}(o:A->A):PROP:=
  inverse_a_droite:\/x:A, x+(o x) == 0.
Class Inverse_a_gauche{A:Monoide}(o:A->A):PROP:=
  inverse_a_gauche:\/x:A, (o x)+x == 0.
Class Inverse(A:Type):= inverse:A->A.

Definition tel_groupe:=
    || m:Monoide;
    || o:Inverse m;
    || _:Inverse_a_droite o;
    || _:Inverse_a_gauche o.

Class Groupe:Type := groupe: el tel_groupe.
Global Instance Groupe_Monoide(m:Groupe): Monoide:=
  @eln tel_groupe m 0.
Coercion Groupe_Monoide: Groupe >-> Monoide.
Global Instance groupe_inverse(m:Groupe):Inverse m:= @eln tel_groupe m 1.
Definition groupe_inverse_a_gauche(m:Groupe):=  @eln tel_groupe m 3.
Definition groupe_inverse_a_droite(m:Groupe):=  @eln tel_groupe m 2.

Global Instance groupe_inverse_i(m:Groupe):Inverse m:=
  groupe_inverse m.

Notation "- x" := (inverse x).

Lemma l5:\/m:Groupe, \/x:m, x+(-x) == 0.
intros. 
Time apply groupe_inverse_a_droite.
Qed.

End Groupe.

(****************************** anneau *)
Section Anneau.
Class Addition(A:Type):= addition:Loi A.
Class Multiplication(A:Type):= multiplication:Loi A.
Class Zero(A:Type):= zero:Neutre A.
Class Un(A:Type):= un:Neutre A.
Notation "x + y" := (addition x y).
Notation "0" := zero.
Notation "x * y" := (multiplication x y).
Notation "1" := un.

Class Distributive_a_droite{A:Magma_associatif}(op:Loi A):PROP:=
  distributive_a_droite:\/x y z:A, op (loi x y) z == loi (op x z) (op y z).
Set Printing All.
Class Distributive_a_droite{A:Magma_associatif}(op:Loi A):PROP:=
  distributive_a_droite:\/x y z:A, op (loi x y) z == loi (op x z) (op y z).


(****************************** exemple d'instance *)

Inductive Bool:Type:= true|false.
Definition plusb(a b:Bool):= if a then if b then false else true else b.
Lemma plusb_assoc:\/a b c, plusb (plusb a b) c = plusb a (plusb b c).
induction a;induction b; induction c; simpl; auto.
Qed.

Definition Bmagma_associatif: Magma_associatif:=
   @pair Type Bool _
  (pair plusb _
  (pair plusb_assoc _
  el_T0)).
Print Bmagma_associatif.

Notation "\\ x ; e1" := (pair x _ e1)(at level 200, right associativity).  
Notation "\\ x ; " := (pair x _ el_T0)(at level 200, right associativity).  
Print Bmagma_associatif.

Instance Magma_associatif_Bool:Magma_associatif := Bmagma_associatif.

Goal  \/x y z:Bmagma_associatif, (x+y)+z = x+(y+z).
intros. 
rewrite magma_associatif_plus_assoc.
trivial.
Qed.