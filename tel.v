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

Definition telr(t:tel):tel1 t -> tel:=
  match t as t0 return (tel1 t0 -> tel) with
   | T0 => fun _ : tel1 T0 => T0
   | Tc T f => \ e, f e
end.
(*
Definition telr{t:tel}:el t -> tel:=
  match t as t0 return (el t0 -> tel) with
   | T0 => fun _ : el T0 => T0
   | Tc T f => \ e, f (el1 e)
end.
*)
Definition elr{t:tel}:\/e:el t, el (telr _ (el1 e)):=
  match t as t0 return (\/ e0 :el t0, el (telr _ (el1 e0))) with
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

(****************************** structure basée sur un sétoïde *)
Section on_setoide.
Context`{S:Setoide->Type}.

Definition tel_on_setoide_:=
    || A:Setoide;
    || R: S A.

Class On_Setoide_:Type := on_setoide_: el tel_on_setoide_.
Global Instance On_Setoide_Setoide(m:On_Setoide_): Setoide:=
  @eln tel_on_setoide_ m 0.
Coercion On_Setoide_Setoide: On_Setoide_ >-> Setoide.
End on_setoide.

(****************************** magma *)

(******************** magma basé sur un sétoïde *)
Section Magma_.

Context`{A:Setoide}.
Class Compatible2(f:Loi A):PROP:=
  compatible2: \/ x x1:A, \/ y y1:A, x == x1 et y == y1 -> f x y == f x1 y1.

Definition tel_magma_:=
  || op : Loi A;
  || _ : Compatible2 op.

Class Magma_:Type := magma_: el tel_magma_.

Global Instance magma_loi(m:Magma_):Loi A:=
  @eln tel_magma_ m 0. 
Global Instance magma_loi_compatible(m:Magma_):Compatible2 (@magma_loi m):=
  @eln tel_magma_ m 1. 

End Magma_.

(******************** magma avec son sétoïde *)

Definition Magma:Type := (@On_Setoide_ (@Magma_)).
Identity Coercion Magmaid: Magma>-> On_Setoide_.

Global Instance Magma_Magma_(m:Magma): @Magma_ m :=
  @eln tel_on_setoide_ m 1.
Coercion Magma_Magma_: Magma >-> Magma_.

(****************************** commutatif *)
Section Magma_commutatif_.
Context`{A:Setoide}.

Class Commutative(f:Loi A):PROP:=
  commutative: \/ x y: A, f x y == f y x.

Definition tel_magma_commutatif_:=
  || M : Magma_;
  || _ : Commutative (magma_loi M).

Class Magma_commutatif_:Type := magma_commutatif_: el tel_magma_commutatif_.
Global Instance Magma_commutatif_Magma_(m:Magma_commutatif_):Magma_:=
  @eln tel_magma_commutatif_ m 0.
Coercion Magma_commutatif_Magma_: Magma_commutatif_ >-> Magma_.

Global Instance magma_commutatif_commutative(m:Magma_commutatif_):Commutative (magma_loi m):=
  @eln tel_magma_commutatif_ m 1. 

End Magma_commutatif_.

Definition Magma_commutatif:Type := (@On_Setoide_ (@Magma_commutatif_)).
Identity Coercion Magma_commutatifid: Magma_commutatif>-> On_Setoide_.

Global Instance Magma_commutatif_Magma_commutatif_(m:Magma_commutatif): @Magma_commutatif_ m :=
  @eln tel_on_setoide_ m 1.
Coercion Magma_commutatif_Magma_commutatif_: Magma_commutatif >-> Magma_commutatif_.

(* test *)
Section test.
Notation "x + y" := (loi x y).
Goal \/A:Magma_commutatif, \/x y:A, x + y == y + x.
intros. 
Time apply magma_commutatif_commutative.
Qed.
End test.

(****************************** magma associatif *)
Section Magma_associatif_.
Context`{A:Setoide}.

Class Associative(f:Loi A):PROP:=
  associative: \/ x y z : A, (f (f x y) z) == (f x (f y z)).

Definition tel_magma_associatif_:=
  || M : Magma_;
  || _ : Associative (magma_loi M).

Class Magma_associatif_:Type := magma_associatif_: el tel_magma_associatif_.
Global Instance Magma_associatif_Magma_(m:Magma_associatif_):Magma_:=
  @eln tel_magma_associatif_ m 0.
Coercion Magma_associatif_Magma_: Magma_associatif_ >-> Magma_.

Global Instance magma_associatif_associative(m:Magma_associatif_):Associative (magma_loi m):=
  @eln tel_magma_associatif_ m 1. 

End Magma_associatif_.

Definition Magma_associatif:Type := (@On_Setoide_ (@Magma_associatif_)).
Identity Coercion Magma_associatifid: Magma_associatif>-> On_Setoide_.

Global Instance Magma_associatif_Magma_associatif_(m:Magma_associatif): @Magma_associatif_ m :=
  @eln tel_on_setoide_ m 1.
Coercion Magma_associatif_Magma_associatif_: Magma_associatif >-> Magma_associatif_.

(****************************** monoide *)
Section Monoide_.
Context`{A:Setoide}.

Class Neutre_a_droite(f:Loi A)(e:A):PROP:=
  neutre_a_droite: \/x:A, f x e == x.
Class Neutre_a_gauche(f:Loi A)(e:A):PROP:=
  neutre_a_gauche: \/x:A, f e x == x.

Definition tel_monoide_:=
    || m:Magma_associatif_;
    || e:Neutre A;
    || _:Neutre_a_droite _ e;
    || _:Neutre_a_gauche _ e.

Class Monoide_:Type := monoide_: el tel_monoide_.
Global Instance Monoide_Magma_associatif_(m:Monoide_): Magma_associatif_:=
  @eln tel_monoide_ m 0.
Coercion Monoide_Magma_associatif_: Monoide_ >-> Magma_associatif_.
Global Instance monoide_neutre(m:Monoide_):Neutre A:= @eln tel_monoide_ m 1.
Global Instance monoide_neutre_a_droite(m:Monoide_):Neutre_a_droite _ (@monoide_neutre m):=
  @eln tel_monoide_ m 2.
Global Instance monoide_neutre_a_gauche(m:Monoide_):Neutre_a_gauche _ (@monoide_neutre m):=
  @eln tel_monoide_ m 3.
End Monoide_.

Definition Monoide:Type := (@On_Setoide_ (@Monoide_)).
Identity Coercion Monoideid: Monoide>-> On_Setoide_.

Global Instance Monoide_Monoide_(m:Monoide): @Monoide_ m :=
  @eln tel_on_setoide_ m 1.
Coercion Monoide_Monoide_: Monoide >-> Monoide_.

(* test *)
Section test2.
Notation "x + y" := (loi x y).
Notation "0" := neutre.

Goal \/A:Monoide, \/x:A, x+0 == x.
intros. 
Time apply monoide_neutre_a_droite.
Qed.

Goal \/m:Monoide, \/x y z:m, (x+y)+z == x+(y+z).
intros. 
Time apply magma_associatif_associative.
Time Qed. 
End test2.

(****************************** groupe *)
Section Groupe_.
Context`{A:Setoide}.

Class Inverse_a_droite{f:Loi A}{e:Neutre A}(o:A->A):PROP:=
  inverse_a_droite:\/x:A, f x (o x) == e.
Class Inverse_a_gauche{f:Loi A}{e:Neutre A}(o:A->A):PROP:=
  inverse_a_gauche:\/x:A, f (o x) x == e.
Class Inverse(A:Type):= inverse:A->A.

Class Compatible(f:A->A):PROP:=
  compatible: \/ x x1:A, x == x1  -> f x == f x1.

Definition tel_groupe_:=
    || m:Monoide_;
    || o:Inverse A;
    || _:Compatible o;
    || _:Inverse_a_droite o;
    || _:Inverse_a_gauche o.

Class Groupe_:Type := groupe_: el tel_groupe_.
Global Instance Groupe_Monoide(m:Groupe_): Monoide_:=
  @eln tel_groupe_ m 0.
Coercion Groupe_Monoide: Groupe_ >-> Monoide_.
Global Instance groupe_inverse(m:Groupe_):Inverse A:= @eln tel_groupe_ m 1.
Global Instance groupe_inverse_a_droite(m:Groupe_):Inverse_a_droite (@groupe_inverse m):=
  @eln tel_groupe_ m 3.
Global Instance groupe_inverse_a_gauche(m:Groupe_):Inverse_a_gauche (@groupe_inverse m):=
  @eln tel_groupe_ m 4.
End Groupe_.

Definition Groupe:Type := (@On_Setoide_ (@Groupe_)).
Identity Coercion Groupeid: Groupe>-> On_Setoide_.

Global Instance Groupe_Groupe_(m:Groupe): @Groupe_ m :=
  @eln tel_on_setoide_ m 1.
Coercion Groupe_Groupe_: Groupe >-> Groupe_.

(* test *)
Section test3.
Notation "x + y" := (loi x y).
Notation "0" := neutre.
Notation "- x" := (inverse x).

Goal \/A:Groupe, \/x:A, x+(-x) == 0.
intros. 
Time apply groupe_inverse_a_droite.
Qed.

End test3.

(****************************** groupe commutatif *)
Section Groupe_commutatif_.
Context`{A:Setoide}.

Definition tel_groupe_commutatif_:=
  || G : Groupe_;
  || _ : Commutative (magma_loi G).

Class Groupe_commutatif_:Type := groupe_commutatif_: el tel_groupe_commutatif_.
Global Instance Groupe_commutatif_Groupe_(m:Groupe_commutatif_):Groupe_:=
  @eln tel_groupe_commutatif_ m 0.
Coercion Groupe_commutatif_Groupe_: Groupe_commutatif_ >-> Groupe_.

Global Instance groupe_commutatif_commutative(m:Groupe_commutatif_):Commutative (magma_loi m):=
  @eln tel_groupe_commutatif_ m 1.
End Groupe_commutatif_.

Definition Groupe_commutatif:Type := (@On_Setoide_ (@Groupe_commutatif_)).
Identity Coercion Groupe_commutatifid: Groupe_commutatif>-> On_Setoide_.

Global Instance Groupe_commutatif_Groupe_commutatif_(m:Groupe_commutatif): @Groupe_commutatif_ m :=
  @eln tel_on_setoide_ m 1.
Coercion Groupe_commutatif_Groupe_commutatif_: Groupe_commutatif >-> Groupe_commutatif_.

Section test4.
Notation "x + y" := (loi x y).
Goal \/A:Groupe_commutatif, \/x y:A, x + y == y + x.
intros. 
Time apply groupe_commutatif_commutative.
Qed.
End test4.

(****************************** anneau *)
Section Anneau_.
Context`{A:Setoide}.

Class Distributive_a_droite(f:Loi A)(g:Loi A):PROP:=
  distributive_a_droite:\/x y z:A, g (f x y) z == f (g x z) (g y z).
Class Distributive_a_gauche(f:Loi A)(g:Loi A):PROP:=
  distributive_a_gauche:\/x y z:A, g z (f x y) == f (g z x) (g z y).

Definition tel_anneau_:=
    || G: @Groupe_commutatif_ A;
    || M: @Monoide_ A;
    || _:Distributive_a_droite (magma_loi G) (magma_loi M);
    || _:Distributive_a_gauche (magma_loi G) (magma_loi M).

Class Anneau_:Type := anneau_: el tel_anneau_.
Global Instance Anneau_Groupe_commutatif(m:Anneau_): Groupe_commutatif_:=
  @eln tel_anneau_ m 0.
(*Coercion Anneau_Groupe_commutatif: Anneau_ >-> Groupe_commutatif_.*)
Global Instance Anneau_Monoide(m:Anneau_): Monoide_:=
  @eln tel_anneau_ m 1.
(*Coercion Anneau_Monoide: Anneau_ >-> Monoide_.*)

Definition anneau_distributive_a_gauche(m:Anneau_):=  @eln tel_anneau_ m 3.
Definition anneau_distributive_a_droite(m:Anneau_):=  @eln tel_anneau_ m 2.

Definition addition_anneau_{a:Anneau_}:= 
  magma_loi (Anneau_Groupe_commutatif a).
Definition multiplication_anneau_{a:Anneau_}:= 
  magma_loi (Anneau_Monoide a).

End Anneau_.

Definition Anneau:Type := (@On_Setoide_ (@Anneau_)).
Identity Coercion Anneauid: Anneau>-> On_Setoide_.
Global Instance Anneau_Anneau_(m:Anneau): @Anneau_ m :=
  @eln tel_on_setoide_ m 1.
Coercion Anneau_Anneau_: Anneau >-> Anneau_.

Section test5.

Notation "x + y" := (addition_anneau_ x y).
Notation "x * y" := (multiplication_anneau_ x y).

Time Goal \/A:Anneau, \/ x y z:A, (x + y) * z == x * z + y * z.
intros. 
Time apply anneau_distributive_a_droite.
Qed.

End test5.

(****************************** exemple d'instance *)

Inductive Bool:Type:= true|false.
Definition eqb:Relation Bool:= 
\ a b:Bool, if a then if b then True else False
                 else if b then False else True.
Lemma t1:Reflexive eqb.
red.  induction x; simpl; auto. Qed.
Lemma t2:Symetrique eqb.
red.  induction x; induction y; simpl; auto. Qed.
Lemma t3:Transitive eqb.
red.  induction x; induction y; induction z; simpl;
 unfold conjonction, conj_prop in *; intuition. Qed.
Check (\\ (Bool:Type); \\ eqb):Graphe.
Check (\\ t1; \\ t2; \\t3):Equivalence.
Definition Bool_setoide:=
 (\\ ((\\ (Bool:Type); \\ eqb):Graphe);
  \\ ((\\ t1; \\ t2; \\t3):Equivalence)):Setoide.


Definition plusb:Loi Bool_setoide:= \a b, if a then if b then false else true else b.
Definition multb:Loi Bool_setoide:= \a b, if a then b else false.

Lemma t4:Associative plusb.
red. induction x;induction y; induction z; simpl; reflexivity. Qed.

Lemma t6: Compatible2 plusb.
red. induction x;induction x1; induction y; induction y1; simpl;
unfold conjonction, conj_prop in *; intuition; try reflexivity. Qed.

Definition oppb:Inverse Bool_setoide:= \a, a.
Lemma t8:Compatible oppb.
red. induction x;induction x1; simpl; auto. Qed.

Lemma t9:@Inverse_a_droite _ plusb false oppb.
red. induction x; simpl; auto; reflexivity. Qed.

Lemma t10:@Inverse_a_gauche _ plusb false oppb.
red. induction x; simpl; auto; reflexivity. Qed.

Lemma t11:@Neutre_a_droite _ plusb false.
red. induction x; simpl; auto; reflexivity. Qed.
Lemma t12:@Neutre_a_gauche _ plusb false.
red. induction x; simpl; auto; reflexivity. Qed.

Lemma t13:Commutative plusb.
red. induction x; induction y; simpl; auto; try reflexivity. Qed.

Time Definition Bool_groupe_additif_:@Groupe_commutatif_ Bool_setoide:=
let B1 := \\ plusb; \\ t6 in
let B2 := \\ B1; \\ t4 in
let B3 := \\ B2; \\ false; \\ t11; \\ t12 in 
let B4 := \\ B3; \\ oppb; \\ t8; \\ t9; \\ t10 in
  \\ B4; \\ t13.
(* 0s *)
(* alors que le suivant met 37s: *)
(*
Time Definition Bool_groupe_additif_:@Groupe_commutatif_ Bool_setoide:=
  (\\
      (\\ (\\ (\\ (\\ plusb; \\ t6);
               \\ t4);
           \\ false; 
           \\ t11;
           \\ t12);
       \\ oppb;
       \\ t8;
       \\ t9;
       \\ t10);
  \\ t13).
*)

Time Definition Bool_groupe_additif:Groupe_commutatif:=
 (\\ Bool_setoide;
  \\ Bool_groupe_additif_).

Lemma t5:Associative multb.
red. induction x;induction y; induction z; simpl; reflexivity. Qed.
Lemma t7: Compatible2 multb.
red. induction x;induction x1; induction y; induction y1; simpl;
unfold conjonction, conj_prop in *; intuition; try reflexivity. Qed.

Lemma t14:@Neutre_a_droite _ multb true.
red. induction x; simpl; auto; reflexivity. Qed.
Lemma t15:@Neutre_a_gauche _ multb true.
red. induction x; simpl; auto; reflexivity. Qed.
Time Definition Bool_monoide_multiplicatif_: @Monoide_ Bool_setoide:=
      (\\ (\\ (\\ multb; \\ t7);
           \\ t5);
       \\ true; 
       \\ t14;
       \\ t15).

Lemma t16:@Distributive_a_droite _ plusb multb.
red. induction x;induction y; induction z; simpl; reflexivity. Qed.
Lemma t17:@Distributive_a_gauche _ plusb multb.
red. induction x;induction y; induction z; simpl; reflexivity. Qed.

Time 
Definition Bool_anneau:Anneau:=
  \\ Bool_setoide;
  \\ (\\ Bool_groupe_additif_;
      \\ Bool_monoide_multiplicatif_;
      \\ t16;
      \\ t17).

Notation "x + y" := (magma_loi (Anneau_Groupe_commutatif Bool_anneau) x y).
Notation "x * y" := (multiplication_anneau_ x y).

Time Goal \/ x y:Bool_anneau, (x + false) * y == x * y.
intros. generalize (@groupe_inverse_a_droite _ (Anneau_Groupe_commutatif Bool_anneau)).
intros. red in H.
Set Printing All.
Show.
 red in H. unfold magma_loi in X. simpl in X. rewrite H.