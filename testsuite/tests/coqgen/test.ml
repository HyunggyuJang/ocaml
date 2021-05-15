(* ../../../ocamlc -c -coq test.ml *)

let ref' = ref;;

let id x = x;;

let incr r =
  let x = !r in r := x + 1;;

let r = ref 1 in incr r;;

let rec loop x = loop x;;

let rec fib n =
  if n = 0 then 1 else if n = 1 then 1 else fib (n-1) + fib (n-2);;

let f10 = fib 10;;
fib 10;;

let omega n =
  let r = ref (fun x -> x) in
  let delta i = !r i in
  r := delta; delta n ;;

(* loops *)
omega 1;;
