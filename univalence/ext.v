(* coq-8.3 *)
(* Some facts founded on the development of Vladimir Voevodsky (https://github.com/vladimirias/Foundations/tree/master/Proof%20of%20Extensionality)
include
- simplification of his proof of extentionnality (2)
- dependent extentionnality, following his suggestion. (3)
- contradiction between univalence and uniqueness of identity proofs (4) (then also with injectivity of dependent
 equality, axiom K of Streicher, etc, see http://coq.inria.fr/stdlib/Coq.Logic.EqdepFacts.html# 
- full dependent extentionnality from JM dependent extentionnality and injectivity of dependent equality (5)
*)

Set Implicit Arguments.

(* 1. Basic notions *)

Inductive paths (T:Type)(t:T): T -> Type :=   idpath: paths t t.

Notation "x == y" := (paths x y) (at level 70).

Definition pr1 :=  fun (T : Type) (P : T -> Type) (z : sigT P) =>
      match z with  | existT t _ => t  end.

Definition pr2 :=  fun (T : Type) (P : T -> Type) (z : sigT P) =>
      match z as z0 return (P (pr1 z0)) with  | existT _ x => x end.

Definition singleton (T:Type) : Type :=  {c:T & forall t:T, t == c}.

Definition hfiber (X Y:Type)(f:X -> Y)(y:Y) : Type :=  {p:X & (f p) == y}. 

Definition bijective (X Y:Type)(F:X -> Y) : Type := 
   forall y:Y, singleton (hfiber F y) .

Definition weq (X Y:Type) : Type := {f:X->Y & bijective f} .

Notation "x ~~ y" := (weq x y) (at level 70).

Definition injective(X Y:Type)(f:X->Y):= forall x y:X, f x == f y -> x == y.

Lemma idbij:forall A:Type, A ~~ A.
intros; unfold weq. exists (fun x => x). unfold bijective, singleton. intros. 
unfold hfiber. exists (existT (fun p : A => p == y) y (idpath y)). intro.
destruct t. destruct p. reflexivity. Defined.

Definition V1 (X Y:Type)  : X == Y -> X ~~ Y.
Proof. intros. destruct H. apply idbij. Defined. 

(* Univalence axiom: V1 is bijective.
One only need a weaker form: there exists V, a section of V1 *)

Axiom V: forall X Y:Type,  X ~~ Y -> X == Y.

Axiom V1V:forall X Y:Type, forall u: X ~~ Y, V1 (V u) == u.

(* 2. Proof of extentionnality of functions *)

Section ext.

Variables X Y:Type.
Variables f1 f2:X->Y.
Hypothesis f1f2ext:forall x, f1 x == f2 x.

Definition ps(T:Type):= {x:T & {y:T& x == y}}.
Definition f(x:X) : ps Y:= 
   existT (fun x => {y:_& x == y}) (f1 x) (existT (fun y=> f1 x == y) (f2 x) (f1f2ext x)).

Definition g1(a:ps Y):= match a with existT t x => t end.
Definition g2(a:ps Y):=  match a with existT t x => (match x with existT t2 p => t2 end) end.

Notation "( x , p )" := (@existT _ _ x p).

Definition delta(x:Y): ps Y :=   existT _ x (existT _ x (idpath x)).

Lemma deltag1id: forall y:ps Y, delta (g1 y) == y.
intros. unfold delta, g1. destruct y. destruct s. destruct p. reflexivity.
Defined.

Lemma deltabij: Y ~~ (ps Y).
intros. exists delta.  unfold bijective, singleton, hfiber. intros.
exists (existT (fun p : Y => delta p == y)  (g1 y) (deltag1id y)).
intros. destruct t. destruct p. reflexivity. Defined.

Definition k(h:ps Y -> Y):= fun x:Y => h (delta x).

(* Axiom eta, no need in Coq trunk now *)

Axiom etacor: forall (X Y:Type), forall (f:X -> Y), f == (fun x:X => f x).

Lemma kinj: injective k.
intros. unfold k. replace delta with (pr1 deltabij). rewrite <- (V1V deltabij). 
generalize (V deltabij).  intro. destruct p. unfold injective; intros.
simpl in H. repeat rewrite <- etacor in H. assumption. reflexivity. Defined.

Lemma g1g2: g1 == g2.
apply kinj. reflexivity. Defined.

Lemma quasiextentionnality: (fun x => f1 x) == (fun x => f2 x).
replace (fun x => f1 x) with (fun x => g1 (f x));[idtac|reflexivity].
replace (fun x => f2 x) with (fun x => g2 (f x));[idtac|reflexivity].
rewrite g1g2. reflexivity. Defined.

Theorem extentionnality: f1 == f2.
rewrite (etacor f1). rewrite (etacor f2).
apply quasiextentionnality. Defined.

End ext.

(* 3. Extentionnality of dependant functions *)

Section extdep.

Variables X:Type.
Variables Pd:X->Type.
Variables f1 f2:forall x:X, Pd x.
Hypothesis f1f2ext:forall x, f1 x == f2 x.

Definition psd(T:Type)(Q:T->Type):= {x:T& {y:Q x & {z:Q x & y == z}}}.

Definition g1d(a:psd Pd):sigT Pd:= existT _ (pr1 a) (pr1 (pr2 a)).
Definition g2d(a:psd Pd):sigT Pd := existT _ (pr1 a) (pr1 (pr2 (pr2 a))).

Lemma g1dg2d: g1d == g2d.
apply extentionnality. intros. destruct x. destruct s. destruct s. 
unfold g1d, g2d. simpl. destruct p. reflexivity.  Defined.

Inductive JMeq (A:Type) (x:A): forall (B:Type), B -> Type :=
    JMeq_refl : JMeq x x.

Definition fd(x:X): psd Pd:= 
  existT (fun x => {y:Pd x & {z:Pd x & y == z}}) x
   (existT (fun x => {y:_& x == y}) (f1 x) 
      (existT (fun y=> f1 x == y) (f2 x) (f1f2ext x))).

Lemma quasiextentionnalityJMeq:  JMeq (fun x => f1 x)  (fun x => f2 x).
replace (fun x => f1 x) with (fun x => pr2 (g1d (fd x)));[idtac|reflexivity].
change ((fun s : psd Pd -> sigT Pd=> JMeq (fun x : X => pr2 (s (fd x))) (fun x : X => f2 x)) g1d).
rewrite g1dg2d. reflexivity. Defined.

Axiom etacord: forall (X: Type) (P: X->Type), forall (f:forall x:X, P x), f == (fun x:X => f x).

Theorem extentionnalityJMeq: JMeq f1 f2.
rewrite (@etacord X Pd   f1). rewrite (@etacord X Pd f2).
apply quasiextentionnalityJMeq. Defined.

End extdep.

(* 4. Univalence contradicts uniqueness of identity proofs. *)

Section univalence_contradicts_uniqueness_of_identity_proofs.

Hypothesis UIP: forall X:Type, forall x y:X, forall p q:x == y, p == q.

Inductive Bool:Type:= true | false.
Definition b1(b:Bool) := b.
Definition b2(b:Bool):= match b with true => false | false => true end.

Lemma b1bij: bijective b1.
apply (pr2 (idbij Bool)). Defined.

Lemma b2bij: bijective b2.
unfold bijective. intros. unfold singleton. destruct y. unfold hfiber.
exists (existT (fun p => b2 p == true)  false (idpath true)). 
intro. destruct t. destruct x. unfold b2 in p.
inversion p.  unfold b2 in p. assert (p == idpath true).
apply UIP. destruct H. reflexivity.
exists (existT (fun p => b2 p == false)  true (idpath false)). 
intro. destruct t. destruct x. unfold b2 in p.
assert (p == idpath false).
apply UIP. destruct H. reflexivity. unfold b2 in p.
inversion p. 
Defined.

Definition b1b: Bool ~~ Bool := idbij Bool.
Definition b2b: Bool ~~ Bool .
exists b2. apply b2bij. Defined.

Lemma l1: b1b == b2b.
rewrite <- (V1V b1b).  rewrite <- (V1V b2b).
assert (V b1b == V b2b). apply UIP. destruct H. reflexivity.
Defined.

Lemma l2: forall X:Type, forall P:X->Type, forall x y:X, forall px:P x, forall py:P y, 
 existT P x px == existT P y py -> x == y.
intros. inversion H. reflexivity. Defined.

Theorem UVcontradictsUIP: False.
assert (b1 == b2). generalize l1. intro.  unfold b1b, b2b in H.
apply l2 with (P:= fun f : Bool -> Bool => bijective f) (px := pr2 (idbij Bool)) (py := b2bij).
exact H. assert (b1 true == b2 true). rewrite H. reflexivity. unfold b1 in H0.  simpl in H0.
inversion H0. Defined.

End univalence_contradicts_uniqueness_of_identity_proofs.

(* 5. Injectivity of dependent equality implies both dependent extentionnality and uniqueness of identity proofs.*)

Section s5.

Variables X:Type.
Variables Pd:X->Type.
Variables f1 f2:forall x:X, Pd x.
Hypothesis f1f2ext:forall x, f1 x == f2 x.

 Inductive eq_dep (U:Type)(P:U->Type)(p:U) (x:P p) : forall q:U, P q -> Prop :=
    eq_dep_intro : eq_dep P p x p x.

Lemma JMeq_eq_dep_id :
 forall (A B:Type) (x:A) (y:B), JMeq x y -> eq_dep (fun X => X) A x B y.
intros. destruct H. reflexivity. Defined.

Definition Eq_dep_eq :=
    forall (U:Type)(P:U->Type) (p:U) (x y:P p), eq_dep P p x p y -> x == y.

Theorem Eq_dep_eq_implies_extentionnality:  Eq_dep_eq -> f1 == f2.
intros. unfold Eq_dep_eq in H. apply (H _ (fun X => X)).
apply JMeq_eq_dep_id. apply extentionnalityJMeq. apply  f1f2ext. Defined.
  
Lemma Eq_dep_eq_implies_uniqueness_of_identity_proofs:
  Eq_dep_eq -> forall X:Type, forall x y:X, forall p q:x == y, p == q.
intros. unfold Eq_dep_eq in H. apply H with (P := fun y => x == y).
 elim q. elim p. reflexivity. Defined.

End s5.