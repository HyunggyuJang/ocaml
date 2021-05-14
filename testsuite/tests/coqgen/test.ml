(* ../../../ocamlc -c -coq test.ml *)

let ref' = ref;;

let id x = x;;

let incr r =
  let x = !r in r := x + 1;;

let r = ref 1 in incr r;;

let rec loop x = loop x;;

let omega n =
  let r = ref (fun x -> x) in
  let delta i = !r i in
  r := delta; delta n ;;

(* loops *)
omega 1;;
