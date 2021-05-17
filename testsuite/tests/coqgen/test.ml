(* ../../../ocamlc -c -coq test.ml *)

let ref' = ref;;

let id x = x;;

let incr r =
  let x = !r in r := x + 1;;

let r = ref 1 in incr r;;

let rec loop x = loop x;;

let rec fib n =
  if n < 2 then 1 else fib (n-1) + fib (n-2);;

let f10 = fib 10;;
fib 10;;

let rec ack m n =
  if m = 0 then n + 1 else
  if n = 0 then ack (m-1) 1 else
  ack (m-1) (ack m (n-1)) ;;

ack 3 7;;

let omega n =
  let r = ref (fun x -> x) in
  let delta i = !r i in
  r := delta; delta n ;;

(* loops *)
omega 1;;
