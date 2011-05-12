(*
#load "graphics.cma";;
open Graphics;;
#use "D:\\Mes Documents\\coq\\phyllotaxie.ml";;
#use "C:\\Users\\pottier\\Documents\\coq\\phyllotaxie.ml";;
#use "D:\\Mes Documents\\coq\\phyllotaxie.ml";;
*)

let norm2 v =
  v.(0)*.v.(0) +. v.(1)*.v.(1)

let vsub v u =
  [|v.(0)-.u.(0); v.(1)-.u.(1)|]

let vadd u v =
  [|v.(0)+.u.(0); v.(1)+.u.(1)|]

let scal u v =
   v.(0)*.u.(0) +. v.(1)*.u.(1)  

let potentiel lp m =
  List.fold_left (fun r p ->
     let n = norm2 (vsub p m) in
     let e = 1./.(sqrt n) in
     r +. e) 0. lp

let potentielmin lp =
  let pi = 3.14159 in
  let amin = ref 0. in
  let fmin = ref (potentiel lp [|1.;0.|]) in
  let n = 200 in
  for i = 1 to n do
    let a = (2.*.pi)*.(float i)/.(float n) in
    let f = potentiel lp [|cos a; sin a|] in
    if f < !fmin
    then (amin := a; fmin := f)
  done;
  (!amin,!fmin)

let eloignement k p =
  let f x = x *. (1. +. k) in
  p.(0)<- f p.(0);
  p.(1)<- f p.(1);
  p

let angle q p =
  let pi = 3.14159 in
  let s = q.(0)*.p.(1)-.q.(1)*.p.(0) in
  let c = q.(0)*.p.(0)+.q.(1)*.p.(1) in
  let a = atan (s/.c) in
  if c < 0. then 
     if s > 0. then a +. pi else a -. pi 
  else a

let vitesse = 0.002

(* création périodique *)
let croissance n =
  let lp = ref [[|1.;0.|]] in
  open_graph "800x800";
  clear_graph ();
  let c = 400. in
  let d = 50. in
  while read_key () <> 'd' do () done;
  for i = 1 to n do
     lp:= List.map (eloignement vitesse) !lp; 
     let (a,f) = potentielmin !lp in
     let p = [|cos a; sin a|] in
(*     Format.printf "px=%.2f py=%.2f \n" p.(0) p.(1);*)
     let q::_ = !lp in
     lp := p::!lp;
     clear_graph ();
     List.iter (fun p -> fill_rect (truncate (c+.d*.p.(0)))
		    (truncate (c+.d*.p.(1))) 2 2) !lp;
(*     Format.printf "a=%.2f\n" (angle q p);*)
  done;
  !lp

(* seuil d'énergie pour création *)

(* energie en 1/d
soit spirales, soit verticillé qui évolue en spirales
croissance2 2000 26.40711 0.008;; 13,8 jolies spirales (pas de coin)
croissance2 2000 26.40710 0.008;; 12,8 spirales à coins
croissance2 2000 20. 0.008;; 12,8
19. 12,8
18. 11,7
15. 10,6
10. 10,6 
9.0085 10,6 ;; 
9.008 7,4 ;; spirales+ peu courbées
9. 7,4 ;; spirales+ peu courbées
8.95 7 ;; spirales+ peu courbées
croissance2 5000 8. 0.004;; 6,4
croissance2 5000 6. 0.004;; 6,4



energie en 1/d^4

ca reste plus longtemps verticillé, mais ca finit par évoluer en spirales
croissance2 500 1000. 0.008;; initial 16 equirepartis, apres joli tournesol, 

*)

let np = 400
(* on garde les np premiers points de la liste, qui sont les plus proches du cercle *)

let eloigne lp vitesse =
  let r = ref [] in
  let l = ref lp in
  let i = ref 0 in
  while !l<>[] && !i <= np do
      let p::l1 = !l in
      r := (eloignement vitesse p)::!r;
      l:=l1;
      i:= !i + 1;
   done;
   List.rev !r
      
let affiche p c d =
  let  e = c/.d in
  let f y =
     let t = (1./.e)*.(y-.1.) /. (1. +. (1./.e)*.(y -. 1.)) in
     0.9*.e*.t +. (1.-.t)*.1.
  in
  let r = sqrt (norm2 p) in
  let r1 = f r in
  let x = r1 *.  p.(0) /. r in
  let y = r1 *.  p.(1) /. r in
  fill_rect (truncate (c+.d*.x))
	    (truncate (c+.d*.y))
            2 2

let croissance2 n potentiel_creation vitesse =
  let lp = ref [[|1.;0.|]] in
  open_graph "800x800";
  clear_graph ();
  let c = 400. in
  let d = 20. in
  while read_key () <> 'd' do () done;
  for i = 1 to n do
     lp:= eloigne !lp  vitesse;
     let (a,f) = potentielmin !lp in
     if f <= potentiel_creation
     then (
	   let p = [|cos a; sin a|] in
	   let q::_ = !lp in
	   lp := p::!lp);
     clear_graph ();
     draw_circle (truncate c)  (truncate c) (truncate d);
     List.iter (fun p -> affiche p c d) !lp;
  done;
  !lp;
  ()

        