(*
 #use "C:\\Users\\pottier\\Documents\\coq\\phyllotaxie.ml";;
*)
let norm2 v =
  v.(0)*.v.(0) +. v.(1)*.v.(1)

let vsub u v =
  [|v.(0)-.u.(0); v.(1)-.u.(1)|]

let vadd u v =
  [|v.(0)+.u.(0); v.(1)+.u.(1)|]

let scal u v =
   v.(0)*.u.(0) +. v.(1)*.u.(1)  

let potentiel lp m =
  List.fold_left (fun r p -> let n = norm2 (vsub p m) in
		      let e = 1./.(sqrt n) in
		      r +. e)
                 0. lp

let potentielmin lp =
  let pi = 3.14159 in
  let amin = ref 0. in
  let fmin = ref (potentiel lp [|1.;0.|]) in
  let n = 400 in
  for i = 1 to n do
    let a = (2.*.pi)*.(float i)/.(float n) in
    let f = potentiel lp [|cos a; sin a|] in
    if f < !fmin
    then (amin := a; fmin := f)
  done;
  !amin

let eloignement k p =
  let np = (*sqrt (norm2 p)*) 1. in
  [|p.(0) +. (p.(0)/.np) *. k; 
    p.(1) +. (p.(1)/.np) *. k|]

let angle q p =
  let pi = 3.14159 in
  let s = q.(0)*.p.(1)-.q.(1)*.p.(0) in
  let c = q.(0)*.p.(0)+.q.(1)*.p.(1) in
  let a = atan (s/.c) in
  if c < 0. then 
     if s > 0. then a +. pi else a -. pi 
  else a

let croissance n =
  let lp = ref [[|1.;0.|]] in
  for i = 1 to n do
     lp:= List.map (eloignement 0.05) !lp; (* 0.05 bizarre *)
     let a = potentielmin !lp in
     let p = [|cos a; sin a|] in
(*     Format.printf "px=%.2f py=%.2f \n" p.(0) p.(1);*)
     let q::_ = !lp in
     lp := p::!lp;
     Format.printf "a=%.2f\n" (angle q p);
  done;
  !lp
;;
croissance 1;;
     
        