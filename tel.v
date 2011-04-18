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

Eval compute in el (Tc (\A : Type, T0)).
Definition p1:el (Tc (\A : Type, T0)):=
  pair (\A:Type, Pt) nat pt.
Definition p2:el (Tc (\A, Tc (\op:A->A->A, T0))):=
  pair _ (nat:Type) (pair _ plus pt).
Print p2.
Definition p4:el (Tc (\x:(el (Tc (\A, Tc (\op:A->A->A, T0)))),T0)):=
  pair _ p2 pt.
Unset Printing All.

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

Eval compute  -[el] in teln p2 0.
Eval compute  -[el] in teln p2 1.

Fixpoint eln{t:tel}(e:el t)(n:nat){struct n}:teln e n:=
  match n with 
   | O => el1 e
   | S n1 => eln (elr e) n1
 end.

Eval compute  -[el] in eln p2 0.
Eval compute  -[el plus] in eln p2 1.

Definition Magmatest:tel:= (Tc (\A, Tc (\op:A->A->A, T0))).
Definition magmatest:el Magmatest:= pair _ (nat:Type) (pair _ plus pt).

Notation "|| x : T ; P" := (Tc (\x : T, P))(at level 200, x ident, right associativity).  
Notation "|| x : T" := (Tc (\x : T, T0))(at level 200, x ident, right associativity).  
Notation "|| '_' : T ; P" := (Tc (\_ : T, P))(at level 200, right associativity).  
Notation "|| '_' : T" := (Tc (\_ : T, T0))(at level 200, right associativity).

Print Magmatest.
Notation "\\ a ; b" :=  (pair _ a b)(at level 200, right associativity). 
Notation "\\ a " :=  (pair _ a pt)(at level 200, right associativity). 
Print magmatest.

Fixpoint add_tel{t:tel}: (el t -> tel) -> tel:=
   match t as t0 return (el t0 -> tel) -> tel with
     | T0 => \ft: el T0 -> tel, ft pt
     | Tc T f => \ft: el (Tc f) -> tel, 
         Tc (\x:T, 
                add_tel (\e: el (f x), ft (pair _ x e)))
   end.

Fixpoint coerce_tel{t:tel}:\/ft:el t -> tel, el (add_tel ft) -> el t:=
  match
    t as t1 return (\/ ft :el t1 -> tel, el (add_tel ft) -> el t1)
  with
    | T0 => \ ft : el T0 -> tel, (fun _ : el (add_tel ft) => pt)
    | Tc T t1 =>
      \ ft : el (Tc t1) -> tel,
      (\ e : el (add_tel ft),
        pair _ (el1 e)
        (coerce_tel
          (\ e2 : el (t1 (el1 e)), ft (pair _ (el1 e) e2))
           (elr e)))
  end.

Eval compute -[el] in
  add_tel (\e:el Magmatest, (Tc (\x:el1 e,T0))). 

Eval compute -[el plus] in
  coerce_tel (\e:el Magmatest,(Tc (\x:el1 e,T0)))
  (pair _ (nat:Type) (pair _ plus (pair _ 0 pt))).

(****************************** exemples *)

Class Neutre (A : Type) := neutre : A.
Class Zero (A : Type) := zero : A.
Notation "0" := zero.
Class Loi(A:Type):= loi:A->A->A.
Class Addition (A : Type) := addition : Loi A.
Notation "_+_" := addition.
Notation "x + y" := (addition x y).
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

(****************************** magma associatif *)

Class Associative{A:Setoide}(f:Loi A):PROP:=
  associative: \/ x y z : A, (f (f x y) z) == (f x (f y z)).
Class Compatible2{A:Setoide}(f:Loi A):PROP:=
  compatible2: \/ x x1:A, \/ y y1:A, x == x1 et y == y1 -> f x y == f x1 y1.

Definition tel_magmaa:=
  || A : Setoide;
  || op : Loi A;
  || _ : Associative op;
  || _ : Compatible2 op.

Set Printing All.
Print tel_magmaa.
Unset Printing All.

Class Magmaa:Type := magmaa: el tel_magmaa.
Instance Magmaa_Setoide(m:Magmaa):Setoide:=
  @eln tel_magmaa m 0.
Coercion Magmaa_Setoide: Magmaa >-> Setoide.
Time Check \m:Magmaa, Loi m.
Time Check \m:Magmaa, Loi m = @teln tel_magmaa m 1.

Time Definition magmaa_loi(m:Magmaa):Loi m:= @eln tel_magmaa m 1. 

Time Definition magmaa_loi_assoc(m:Magmaa):Associative (@magmaa_loi m):=
  @eln tel_magmaa m 2. 
Instance magmaa_add(m:Magmaa):Loi m:= magmaa_loi m.

Section test.
Notation "_+_" := loi.
Notation "x + y" := (loi x y).

Lemma l2:\/m:Magmaa, \/x y z:m, (x+y)+z == x+(y+z).
intros. 
Time apply magmaa_loi_assoc. 
Qed.
End test.

(****************************** monoide *)

Class Neutre_a_droite{A:Setoide}(f:A->A->A)(e:A):PROP:=
  neutre_a_droite: \/x:A, (f x e) == x.
Class Neutre_a_gauche{A:Setoide}(f:A->A->A)(e:A):PROP:=
  neutre_a_gauche: \/x:A, (f e x) == x.

Definition tel_monoide:=
    || m:Magmaa;
    || e:Neutre m;
    || _:Neutre_a_droite (magmaa_loi m) e;
    || _:Neutre_a_gauche (magmaa_loi m) e.

Class Monoide:Type := monoide: el tel_monoide.
Instance Monoide_Magmaa(m:Monoide): Magmaa:=
  @eln tel_monoide m 0.
Coercion Monoide_Magmaa: Monoide >-> Magmaa.
Instance monoide_neutre(m:Monoide):Neutre m:= @eln tel_monoide m 1.
Definition monoide_neutre_a_gauche(m:Monoide):=  @eln tel_monoide m 3.
Definition monoide_neutre_a_droite(m:Monoide):=  @eln tel_monoide m 2.

Instance monoide_neutre_i(m:Monoide):Neutre m:= monoide_neutre m.

Section test2.
Notation "_+_" := loi.
Notation "x + y" := (loi x y).
Notation "0" := neutre.

Lemma l3:\/m:Monoide, \/x:m, x+0 == x.
intros. 
Time apply monoide_neutre_a_droite.
Qed.

Lemma l4:\/m:Monoide, \/x y z:m, (x+y)+z == x+(y+z).
intros. 
Time apply magmaa_loi_assoc.
Time Qed. 
End test2.

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

(****************************** exemple d'instance *)

Inductive Bool:Type:= true|false.
Definition plusb(a b:Bool):= if a then if b then false else true else b.
Lemma plusb_assoc:\/a b c, plusb (plusb a b) c = plusb a (plusb b c).
induction a;induction b; induction c; simpl; auto.
Qed.

Definition Bmagmaa: Magmaa:=
   @pair Type Bool _
  (pair plusb _
  (pair plusb_assoc _
  el_T0)).
Print Bmagmaa.

Notation "\\ x ; e1" := (pair x _ e1)(at level 200, right associativity).  
Notation "\\ x ; " := (pair x _ el_T0)(at level 200, right associativity).  
Print Bmagmaa.

Instance Magmaa_Bool:Magmaa := Bmagmaa.

Goal  \/x y z:Bmagmaa, (x+y)+z = x+(y+z).
intros. 
rewrite magmaa_plus_assoc.
trivial.
Qed.