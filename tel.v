(*

      Télescopes généralisés.

(d'après la notion de télescope décrite dans l'article de N.G. De Bruijn
 "Telescoping mappings in typed lambda calculus", 
Information and Computation, vol 91, No 2, pp 189-204, avril 91).

Un télescope est une suite d'abstractions:
[x1:T1][x2:T2(x1)]...[xn:Tn(x1,...,xn-1)]
*)
Set Implicit Arguments.
Load "ring/Algebra_syntax3.v".

(* Un type pour représenter les télescopes: *)

Inductive tel: Type :=
  | T0: tel
  | Tc: forall T:Type, (T -> tel) -> tel .

Definition monoide:tel := 
 (Tc (\A:Type,
 (Tc (\plus:A->A->A,
 (Tc (\zero:A,
 (Tc (\plus_assoc:
           \/x y z:A, plus (plus x y) z = plus x (plus y z),
 (Tc (\plus_zero: \/x:A, plus x zero = x 
           , T0)))))))))).
              
Notation "\\ x : T , P" := (Tc (\x : T, P))(at level 200, right associativity).  
Notation "\\ '_' : T , P" := (Tc (\_ : T, P))(at level 200, right associativity).  
Notation "\\ '_' : T" := (Tc (\_ : T, T0))(at level 200, right associativity).

Print monoide.

(* Ce type contient en fait plus que les télescopes de De Bruijn, 
 puisque si x:T et f:T -> tel, le telescope f(x) peut etre de longueur 
 variable selon x. Benjamin Werner m'a fait remarquer que c'est un type isomorphe
 à celui des ensembles de Peter Aczel. Tant mieux!
 Pour déstructurer un télescope: *)

Fixpoint tel_to_prod(t:tel)(T0T:Type):Type:=
  match t with
    | T0 => T0T
    | Tc T P => \/x:T, (tel_to_prod (P x) T0T)
  end.

Eval compute in tel_to_prod monoide.

Inductive tel_record(t:tel):Type:=
  | build_tel_record:tel_to_prod t (tel_record t).

Fixpoint tel_to_fun(t:tel)(T0T:Type)(t0:T0T):tel_to_prod t T0T:=
  match t with
    | T0 => t0
    | Tc T P => \x:T, (tel_to_fun (P x) T0T t0)
  end.
Eval compute in tel_to_fun monoide.

Definition tel_type(t:tel):Type:=
 match t with T0 => True | Tc T P => T end.

Definition tel_fun(t:tel):tel_type t -> tel.
induction t. intros. exact T0. simpl. exact t. Defined.

(* Un élément d'un télescope [x1:T1][x2:T2(x1)]...[xn:Tn(x1,...,xn-1)] est une suite de variables
 x1,...,xn avec les types correspondants. *)

Inductive el_tel: tel ->Type :=
  |el_T0: (el_tel T0)
  |el_Tc: forall (T:Type) (x:T) (f:T -> tel),
            (el_tel (f x)) -> (el_tel (Tc f)) .

(* exemple *)
Inductive Bool:Type:= true|false.
Definition plusb(a b:Bool):= if a then if b then false else true else b.
Definition zerob:Bool := false.
Lemma plusb_assoc:\/a b c, plusb (plusb a b) c = plusb a (plusb b c).
induction a;induction b; induction c; simpl; auto.
Qed.
Lemma plusb_zero:\/a, plusb a zerob = a.
induction a; simpl; auto.
Qed.

Definition monoide2_Bool: el_tel monoide:=
  @el_Tc Type Bool _
  (el_Tc plusb _
  (el_Tc zero _
  (el_Tc plusb_assoc _
  (el_Tc plusb_zero _ 
  el_T0)))).

Inductive tel_record(t:tel):=
 
(* Fonctions de déstructuration de ces éléments. *)
Definition el_fst: (t:tel) (e:(el_tel t))(tel_type t).
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
Exact (tel_type t).
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

(*

      Inclusion de télescopes.

idées:

- le télescope vide est minimal.
- si pour tout x, f(x) <= g(x), alors (x:T)f(x) <= (x:T)g(x)
- si pour tout x, t <= f(x), alors t <= (x:T)f(x)
- si pour tous x et y f(x,y) <= g(y,x), alors (x:A)(y:B)f(x,y) <= (y:B)(x:A)g(y,x).
- <= est transitive.

*)

Inductive subtel: tel -> tel ->Type :=
     subtel_T0: (t:tel)(subtel T0 t)
    | subtel_Tc:
        (T:Type) (f, g:T ->tel) ((x:T)(subtel (f x) (g x))) ->
        (subtel (Tc f) (Tc g))
    | subtel_tel_Tc:
        (t:tel) (T:Type) (f:T ->tel) ((x:T)(subtel t (f x))) ->(subtel t (Tc f))
    | subtel_transpose_Tc:
        (A, B:Type)
        (f:A -> B ->tel)
        (g:B -> A ->tel) ((x:A) (y:B)(subtel (f x y) (g y x))) ->
        (subtel (Tc [x:A](Tc (f x))) (Tc [x:B](Tc (g x))))
    | subtel_trans:
        (t, t', t'':tel) (subtel t t') -> (subtel t' t'') ->(subtel t t'') .
Hints Resolve subtel_T0 subtel_Tc subtel_tel_Tc subtel_transpose_Tc : core.

(*
        Coercions d'un télescope vers un autre plus petit.
*)

Definition coerce_tel: (t, t':tel) (subtel t t') -> (el_tel t') ->(el_tel t).
Fix 3.
Intros t t' H'; Try Assumption.
Case H'.
Intros T H'0; Try Assumption.
Exact el_T0.
Intros T f g H'0 H'1; Try Assumption.
Apply el_Tc with x := (el_fst H'1).
Apply coerce_tel with t' := (g (el_fst H'1)).
Apply H'0.
Exact (el_rem H'1).
Intros t0 T f H'0 H'1; Try Assumption.
Apply coerce_tel with t' := (tel_fun (el_fst H'1)).
Apply H'0.
Exact (el_rem H'1).
Intros A B f g H'0 H'1; Try Assumption.
Apply el_Tc with x := (el_fst (el_rem H'1)).
Apply el_Tc with x := (el_fst H'1).
Apply coerce_tel with t' := (g (el_fst H'1) (el_fst (el_rem H'1))).
Apply H'0.
Exact (el_rem (el_rem H'1)).
Intros t0 t'0 t'' H'0 H'1 H'2; Try Assumption.
Apply coerce_tel with t' := t'0; Auto with core.
Apply coerce_tel with t' := t''; Auto with core.
Defined.

Lemma subtel_refl: (t:tel)(subtel t t).
Intros t; Try Assumption.
Elim t; Auto with core.
Qed.
Hints Resolve subtel_refl : core.

(*

Quelques exemples montrant comment on peut récupérer avec les télescopes ce qu'on a avec les Record et les coercions de Coq.

t1:=(E:Type)(a1:A1(E))(b1:(B1 E a1))

*)

Variables A1, A2:Type ->Type.
Variable B1:(E:Type) (a:(A1 E))Type.
Variable B2:(E:Type) (a:(A2 E))Type.

Definition t1 := (Tc [E:Type](Tc [a1:(A1 E)](Tc [b1:(B1 E a1)]T0))).

Definition T1 := (el_tel t1).

(*
Les projections d'accès aux champs.
*)

Definition g_E: T1 ->Type := (!el_nth t1 O).

Definition g_a1: (x:T1)(A1 (g_E x)) := (!el_nth t1 (S O)).

Definition g_b1: (x:T1)(B1 (g_E x) (g_a1 x)) := (!el_nth t1 (S (S O))).

(*
Constructeur de T1.
*)

Definition Build_T1: (E1:Type) (va1:(A1 E1)) (B1 E1 va1) ->T1 :=
   [E1:Type] [va1:(A1 E1)] [vb1:(B1 E1 va1)]
   (!el_Tc
      ? E1 (!tel_fun t1)
      (!el_Tc
         ? va1 (!tel_fun ((!tel_fun t1) E1))
         (!el_Tc ? vb1 (!tel_fun ((!tel_fun ((!tel_fun t1) E1)) va1)) el_T0))).

(* 
les élements de T1 comme  types.
*)

Coercion g_E : T1 >-> SORTCLASS.

(*
Un exemple d'élément de T1.
*)
Variable E1:Type.
Variable va1:(A1 E1).
Variable vb1:(B1 E1 va1).


Definition vT1: T1 := (Build_T1 E1 va1 vb1).
Eval Compute in (!tel_nth t1 O vT1).
Eval Compute in (!tel_nth t1 (S O) vT1).
Eval Compute in (!tel_nth t1 (S (S O)) vT1).
Eval Compute in (!el_nth t1 O vT1).
Eval Compute in (!el_nth t1 (S O) vT1).
Eval Compute in (!el_nth t1 (S (S O)) vT1).
Eval Compute in (g_E vT1).
Eval Compute in (g_a1 vT1).
Eval Compute in (g_b1 vT1).

(*
vT1 comme type.
*)

Variable x1:vT1.

(* 
Un télescope qui étend t1.
*)

Definition t0 :=
   (Tc
      [E:Type]
      (Tc [a1:(A1 E)](Tc [a2:(A2 E)](Tc [b1:(B1 E a1)](Tc [b2:(B2 E a2)]T0))))).

Lemma l1: (subtel t1 t0).
Unfold t1 t0; Auto with core.
Defined.
Hints Resolve l1 : core.

Lemma l2: (t:tel) (subtel t0 t) ->(subtel t1 t).
Intros t H'; Try Assumption.
Apply subtel_trans with t0; Auto with core.
Defined.
Hints Resolve l2 : core.
Variable va2:(A2 E1).
Variable vb2:(B2 E1 va2).

Definition T := (el_tel t0).

Definition vT: T :=
   (!el_Tc
      Type E1
      [E:Type]
      (Tc [a1:(A1 E)](Tc [a2:(A2 E)](Tc [b1:(B1 E a1)](Tc [b2:(B2 E a2)]T0))))
      (!el_Tc
         (A1 E1) va1
         [a1:(A1 E1)](Tc [a2:(A2 E1)](Tc [b1:(B1 E1 a1)](Tc [b2:(B2 E1 a2)]T0)))
         (!el_Tc
            (A2 E1) va2 [a2:(A2 E1)](Tc [b1:(B1 E1 va1)](Tc [b2:(B2 E1 a2)]T0))
            (!el_Tc
               (B1 E1 va1) vb1 [b1:(B1 E1 va1)](Tc [b2:(B2 E1 va2)]T0)
               (!el_Tc (B2 E1 va2) vb2 [b2:(B2 E1 va2)]T0 el_T0))))).
Check (coerce_tel l1 vT).

Definition T_T1: T ->T1 := (!coerce_tel ? ? l1).
Check (T_T1 vT).

(*
Coercion de T vers T1.
*)

Coercion T_T1 : T >-> T1.

Check (g_E vT).

Eval Compute in (g_E vT).
Eval Compute in (g_a1 vT).
Eval Compute in (g_b1 vT).

(* Amalgames de télescopes avec une définition plus faible de l'inclusion. *)

Mutual Inductive subtel: tel -> tel ->Type :=
     subtel_T0: (t:tel)(subtel T0 t)
    | subtel_Tc:
        (T, T':Type) (identityT ? T T') ->
        (f:T ->tel)
        (g:T' ->tel)
        ((x:T)
         (x':T')
         (identityT
            ? (existT Type [T0:Type]T0 T x) (existT Type [T0:Type]T0 T' x')) ->
         (subtel (f x) (g x'))) ->(subtel (Tc f) (Tc g))
    | subtel_tel_Tc:
        (t:tel) (T:Type) (f:T ->tel) ((x:T)(subtel t (f x))) ->(subtel t (Tc f)) .
Hints Resolve subtel_T0 subtel_Tc subtel_tel_Tc :core.

Definition coerce_type:
  (T, T':Type) (identityT ? T' T) ->
  (x:T)
  (sigT
     ?
     [x':T']
     (identityT ? (existT Type [T0:Type]T0 T x) (existT Type [T0:Type]T0 T' x'))).
Intros T T' H'; Try Assumption.
Case H'.
Intros x; Try Assumption.
Exists x.
Auto with core.
Defined.

Definition coerce_tel: (t, t':tel) (subtel t t') -> (el_tel t') ->(el_tel t).
Fix 3.
Intros t t' H'; Try Assumption.
Case H'.
Intros T H'0; Try Assumption.
Exact el_T0.
Intros T T' H'0 f g H'1 H'2.
Case (coerce_type H'0 (el_fst H'2)).
Intros x H'3; Try Assumption.
Apply el_Tc with x := x.
Apply coerce_tel with t' := (g (el_fst H'2)).
Apply H'1.
Simpl in H'3; Auto with core.
Exact (el_rem H'2).
Intros t0 T f H'0 H'1; Try Assumption.
Apply coerce_tel with t' := (tel_fun (el_fst H'1)).
Apply H'0.
Exact (el_rem H'1).
Defined.
Parameter subtel_refl:(t:tel)(subtel t t).
Hints Resolve subtel_refl :core.

Definition concat_tel: tel -> tel ->tel.
Fix 1.
Intros t1.
Case t1.
Exact [t2:tel]t2.
Intros T f.
Exact [t2:tel](Tc [x:T](concat_tel (f x) t2)).
Defined.

Mutual Inductive sumT[A, B:Type]: Type :=
     leftT: A ->(sumT A B)
    | rightT: B ->(sumT A B) .

Record prodT[A, B:Type]: Type := {
   prodT1: A;
   prodT2: B }.

Axiom depidT_idT:
      (T:Type)
      (x, y:T)
      (identityT
         (sigT Type [T0:Type]T0) (existT Type [T0:Type]T0 T x)
         (existT Type [T0:Type]T0 T y)) ->(identityT T x y).
Hints Resolve depidT_idT :core.

Axiom depidT_idTfun:
      (T, A:Type)
      (f, g:T ->A)
      (identityT
         (sigT Type [T:Type] T ->A) (existT Type [T:Type] T ->A T f)
         (existT Type [T:Type] T ->A T g)) ->(identityT ? f g).

Axiom depidT_idTtype:
      (T, T':Type)
      (P:Type ->Type)
      (f:(P T))
      (g:(P T')) (identityT ? (existT Type P T f) (existT Type P T' g)) ->
      (identityT ? T T').

Definition identityT_fun:
  (T, T', A:Type)
  (f:T ->A)
  (g:T' ->A)
  (identityT
     (sigT Type [T:Type] T ->A) (existT Type [T:Type] T ->A T f)
     (existT Type [T:Type] T ->A T' g)) ->
  (x:T)
  (x':T')
  (identityT
     (sigT Type [T0:Type]T0) (existT Type [T0:Type]T0 T x)
     (existT Type [T0:Type]T0 T' x')) ->(identityT ? (f x) (g x')).
Intros T T' A f g H'; Try Assumption.
Cut (identityT ? T T').
Intros H'0; Try Assumption.
Generalize H'; Clear H'.
Generalize g; Clear g.
Generalize f; Clear f.
Rewrite <- H'0.
Intros f g H' x x' H'1; Try Assumption.
Rewrite (depidT_idT H'1).
Rewrite (depidT_idTfun H').
Auto with core.
Rewrite (depidT_idTtype H').
Auto with core.
Defined.

Definition subtel_Tc_Tc:
  (t, t':tel) (subtel t t') ->
  (T:Type) (f:T ->tel) (identityT ? t (Tc f)) ->
  (T':Type) (g:T' ->tel) (identityT ? t' (Tc g)) ->
  (sumT
     (prodT
        (identityT ? T T')
        (x:T)
        (x':T')
        (identityT
           ? (existT Type [T0:Type]T0 T x) (existT Type [T0:Type]T0 T' x')) ->
        (subtel (f x) (g x'))) (x:T')(subtel (Tc f) (g x))).
Intros t t' H'; Try Assumption.
Case H'.
Intros H'0 T f H'1; Try Assumption.
Inversion H'1.
Intros T T' H'0 f g H'1 T0 f0 H'2 T'0 g0 H'3; Try Assumption.
Left.
Split.
Apply trans_idT with T.
Injection H'2.
Auto with core.
Apply trans_idT with T'.
Auto with core.
Injection H'3.
Auto with core.
Intros x x' H'4; Try Assumption.
Injection H'2.
Intros H'5 H'6; Try Assumption.
Case (coerce_type H'6 x).
Intros x0 H'7; Try Assumption.
Cut (identityT ? (f0 x) (f x0)).
Intros H'8; Try Assumption.
Rewrite H'8.
Injection H'3.
Intros H'9 H'10; Try Assumption.
Case (coerce_type H'10 x').
Intros x1 H'11; Try Assumption.
Cut (identityT ? (g0 x') (g x1)).
Intros H'12; Try Assumption.
Rewrite H'12.
Apply H'1.
Apply trans_idT with (existT Type [T0:Type]T0 T1 x).
Auto with core.
Apply trans_idT with (existT Type [T0:Type]T0 T'0 x').
Auto with core.
Auto with core.
Apply identityT_fun with T := T'0 T' := T'.
Auto with core.
Auto with core.
Apply identityT_fun with T := T1 T' := T.
Auto with core.
Auto with core.
Intros t0 T f H'0 T0 f0 H'1 T' g H'2; Try Assumption.
Right.
Intros x; Try Assumption.
Rewrite <- H'1.
Injection H'2.
Intros H'3 H'4; Try Assumption.
Case (coerce_type H'4 x).
Intros x0 H'5; Try Assumption.
Cut (identityT ? (g x) (f x0)).
Intros H'6; Try Assumption.
Rewrite H'6.
Apply H'0.
Apply identityT_fun with T := T' T' := T.
Auto with core.
Auto with core.
Defined.

Definition mixtel: (t1, t2:tel) (subtel t1 t2) ->(t3:tel) (subtel t1 t3) ->tel.
Fix 1.
Intros t1.
Case t1.
Intros t2 H' t3 H'0.
Exact (concat_tel t2 t3).
Intros T f.
Fix mixtel2 1.
Intros t2.
Case t2.
Intros H' t3 H'0.
Inversion H'.
Intros T0 g.
Intros H'.
Case (!subtel_Tc_Tc
        (Tc f) (Tc g) H' T f (refl_identityT ? (Tc f)) T1 g
        (refl_identityT ? (Tc g))).
Intros H'0.
Case H'0; Clear H'0.
Intros H'0 H'1.
Fix mixtel3 1.
Intros t3.
Case t3.
Intros H'2.
Inversion H'2.
Intros T0 h H'2.
Case (!subtel_Tc_Tc
        (Tc f) (Tc h) H'2 T f (refl_identityT ? (Tc f)) T2 h
        (refl_identityT ? (Tc h))).
Intros H'3.
Case H'3; Clear H'3.
Intros H'3 H'4.
Apply (!Tc T).
Intros x.
Case (coerce_type (sym_idT ? ? ? H'3) x).
Intros x0 H'5.
Case (coerce_type (sym_idT ? ? ? H'0) x).
Intros x1 H'6.
Exact (mixtel ? ? (H'1 x x1 H'6) ? (H'4 x x0 H'5)).
Intros H'3.
Apply (!Tc T2).
Intros x.
Exact (mixtel3 ? (H'3 x)).
Intros H'0 t3 H'1.
Apply (!Tc T1).
Intros x.
Exact (mixtel2 ? (H'0 x) t3 H'1).
Defined.

Axiom extT:
      (T, T':Type) (f, g:T ->T') ((x:T)(identityT ? (f x) (g x))) ->
      (identityT ? f g).
Hints Resolve extT :core.

Lemma concat_tel_T0: (t:tel)(identityT ? (concat_tel t T0) t).
Induction t.
Simpl.
Auto with core.
Simpl.
Intros T t0 H'; Try Assumption.
Cut (identityT ? [x:T](concat_tel (t0 x) T0) t0).
Intros H'0; Try Assumption.
Rewrite H'0.
Auto with core.
Auto with core.
Qed.
Hints Resolve concat_tel_T0 :core.

Lemma subtel_concat: (t1, t2:tel)(subtel t1 (concat_tel t1 t2)).
Induction t1.
Simpl.
Auto with core.
Simpl.
Intros T t H' t2; Try Assumption.
Apply subtel_Tc.
Auto with core.
Intros x x' H'0; Try Assumption.
Rewrite (depidT_idT H'0).
Apply (H' x' t2).
Qed.
Hints Resolve subtel_concat :core.(*
                                  Lemma mixtel1:
                                    (t1, t2:tel) (s2:(subtel t1 t2)) (t3:tel) (s3:(subtel t1 t3))
                                    (subtel t2 (mixtel s2 s3)).
                                  Induction t1.
                                  Simpl; Auto with core.
                                  Induction t2.
                                  Auto with core.
                                  Intros T0 t0 H' s2; Try Assumption.
                                  Case s2.
                                  Simpl.
                                  Auto with core.
                                  Simpl.
                                  Intros T0 T' i f g s; Try Assumption.
                                  Induction t3.
                                  Intros s3; Try Assumption.
                                  Inversion s3.
                                  Intros T0 t4 H'0 s3; Try Assumption.
                                  Simpl.
                                  Inversion s3; Try Assumption.
                                  Case (subtel_Tc_Tc s3 (refl_identityT tel (Tc f)) (refl_identityT tel (Tc t4))).
                                  Intros p; Try Assumption.
                                  Case p.
                                  Intros prodT1 prodT2; Try Assumption.
                                  Case (coerce_type (sym_idT Type T2 T3 prodT3) x).
                                  Apply extT.
                                  Auto with core.
                                  Intros T0 t0 H' H'0; Try Assumption.
                                  Simpl.
                                  Intros x; Try Assumption.
.......
                                  *)