(* ../../../ocamlc -c -coq test.ml *)

let ref' = ref;;

let id x = x;;

let incr r =
  let x = !r in r := x + 1;;

let r = ref 1 in incr r;;

let rec loop x = loop x;;

let rec fib n =
  if n <= 1 then 1 else fib (n-1) + fib (n-2);;

let f10 = fib 10;;
fib 10;;

let rec ack m n =
  if m <= 0 then n + 1 else
  if n <= 0 then ack (m-1) 1 else
  ack (m-1) (ack m (n-1)) ;;

ack 3 7;;

let rec iter_int n f x =
  if n < 1 then x else iter_int (n-1) f (f x);;

(*
let fib2 n =
  let l1 = ref 1 and l2 = ref 1 in
  iter_int n (fun _z -> let x = !l1 and y = !l2 in l1 := y; l2 := x+y; !l1) 1;;
*)

let fib2 n =
  let l1 = ref 1 in let l2 = ref 1 in
  iter_int n
    (fun _ -> let x = !l1 in let y = !l2 in l1 := y; l2 := x+y)
    ();
  !l1 ;;

fib2 1000 ;;

let rec iota m n =
  if n <= 0 then [] else m :: iota (m+1) (n-1) ;;

iota 1 10;;

let omega n =
  let r = ref (fun x -> x) in
  let delta i = !r i in
  r := delta; delta n ;;

(* loops *)
omega 1;;
