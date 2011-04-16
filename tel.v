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
Definition tel_setoide_diff(m:Graphe):= 
  || _:@Equivalence _ (@graphe_relation m).
(* ya plus d'inconsistence d'univers :-) *)

Definition tel_setoide := 
  Eval compute -[PROP Relation 
                 conjonction Equivalence Reflexive Symetrique Transitive] in
  add_tel tel_setoide_diff.
Print tel_setoide.

Set Printing All.
Print tel_setoide.
Unset Printing All.

Class Setoide:= setoide: el tel_setoide.
Instance Setoide_Graphe(E:Setoide):Graphe:=
  coerce_tel tel_setoide_diff E.
Coercion Setoide_Graphe: Setoide >-> Graphe.
Instance setoide_equality(E:Setoide):Equality E:= graphe_relation E.
Time Instance setoide_equivalence(E:Setoide):Equivalence (R:=_==_) :=
  @eln tel_setoide E 2.

Lemma l0:\/E:Setoide, \/x:E, x == x.
intros. apply (equivalence_reflexive (setoide_equivalence E)).
Qed.
Lemma l1:\/E:Setoide, \/x y:E, x == y -> y == x.
intros. apply (equivalence_symetrique (setoide_equivalence E)). trivial.
Qed.

(****************************** magma associatif *)

Class Associative{A:Setoide}(f:Law A):PROP:=
  associative: \/ x y z : A, (f (f x y) z) == (f x (f y z)).
Class Compatible2{A:Setoide}(f:Law A):PROP:=
  compatible2: \/ x x1:A, \/ y y1:A, x == x1 et y == y1 -> f x y == f x1 y1.

Definition tel_magmaa_diff(A:Setoide):=
  || op : Law A;
  || _ : Associative op;
  || _ : Compatible2 op.
Definition tel_magmaa :=
  Eval compute -[el PROP
                 Setoide Relation Associative Compatible2 Law
                 conjonction Equivalence Reflexive Symetrique Transitive] in
add_tel tel_magmaa_diff.

Set Printing All.
Print tel_magmaa_diff.
Print tel_magmaa.
Eval compute -[el PROP 
                 Setoide Relation Associative Compatible2 Law
                 conjonction Equivalence Reflexive Symetrique Transitive] in
add_tel tel_magmaa_diff.
Check @Associative.
Print tel_magmaa_diff.
Unset Printing All.

Class Magmaa:Type := magmaa: el tel_magmaa.
Instance Magmaa_Setoide(m:Magmaa):Setoide:=
  coerce_tel tel_magmaa_diff m.
Coercion Magmaa_Setoide: Magmaa >-> Setoide.
Time Check \m:Magmaa, Law m.
Time Check \m:Magmaa, Law m = @teln tel_magmaa m 3.

Time Definition magmaa_law(m:Magmaa):Law m:= @eln tel_magmaa m 3. (* 0s *)

Time Definition magmaa_law_assoc(m:Magmaa):Associative (@magmaa_law m):=
  Eval compute
    -[PROP Relation 
      conjonction Equivalence Reflexive Symetrique Transitive] in
  @eln tel_magmaa m 4. (* 3s *)

Print magmaa_law_assoc.

Instance magmaa_add(m:Magmaa):Addition m:= magmaa_law m.

Lemma l2:\/m:Magmaa, \/x y z:m, (x+y)+z == x+(y+z).
intros. 
Time apply magmaa_law_assoc. 
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