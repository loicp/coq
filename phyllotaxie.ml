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

let force lp m =
  List.fold_left (fun r p -> let n = norm2 (vsub p m) in
		      let x = (m.(0)-.p.(0))/.n in
		      let y = (m.(1)-.p.(1))/.n in
		      vadd r [|x;y|])
                 [|0.;0.|] lp

let equilibre lp =
  let a = ref 0.123456789 in
  for i = 1 to 200 do
    let f = force lp [|cos !a; sin !a|] in
(*    Format.printf "a=%f fx=%f fy=%f\n" !a f.(0) f.(1);*)
    let da = scal f [|-.sin !a; cos !a|] in
    a:= !a +. da/.(5.*.(float (List.length lp)));
  done;
  !a

let eloignement k p =
  let np = sqrt (norm2 p) in
  [|p.(0) +. (p.(0)/.np) *. k; 
    p.(1) +. (p.(1)/.np) *. k|]

let croissance n =
  let lp = ref [[|1.;0.|]] in
  for i = 1 to n do
     lp:= List.map (eloignement 0.1) !lp;
     let a = equilibre !lp in
     let p = [| cos a; sin a|] in
(*     Format.printf "px=%.2f py=%.2f \n" p.(0) p.(1);*)
     let q::_ = !lp in
     lp := p::!lp;
     let at = (q.(0)*.p.(1)-.q.(1)*.p.(0))/.(q.(0)*.p.(0)+.q.(1)*.p.(1)) in
     Format.printf "a=%f.2\n" (atan at);
  done;
  !lp
;;
croissance 1;;
     
        