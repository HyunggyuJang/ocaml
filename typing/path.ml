(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t =
    Pident of Ident.t
  | Pdot of t * string
  | Papply of t * t
  | Pextra_ty of t * extra_ty
and extra_ty =
  | Pcstr_ty of string
  | Pext_ty
  | Pcls_ty

let rec same p1 p2 =
  p1 == p2
  || match (p1, p2) with
    (Pident id1, Pident id2) -> Ident.same id1 id2
  | (Pdot(p1, s1), Pdot(p2, s2)) -> s1 = s2 && same p1 p2
  | (Papply(fun1, arg1), Papply(fun2, arg2)) ->
       same fun1 fun2 && same arg1 arg2
  | (Pextra_ty p1, Pextra_ty p2) ->
      same_extra p1 p2
  | (_, _) -> false
and same_extra p1 p2 =
  p1 == p2
  || match (p1, p2) with
    (Pcstr_ty(p1, s1), Pcstr_ty(p2, s2)) ->
    s1 = s2 && same p1 p2
  | (Pext_ty p1, Pext_ty p2) -> same p1 p2
  | (Pcls_ty p1, Pcls_ty p2) -> same p1 p2
  | (_, _) -> false

let rec compare p1 p2 =
  if p1 == p2 then 0
  else match (p1, p2) with
    (Pident id1, Pident id2) -> Ident.compare id1 id2
  | (Pdot(p1, s1), Pdot(p2, s2)) ->
      let h = compare p1 p2 in
      if h <> 0 then h else String.compare s1 s2
  | (Papply(fun1, arg1), Papply(fun2, arg2)) ->
      let h = compare fun1 fun2 in
      if h <> 0 then h else compare arg1 arg2
  | (Pextra_ty p1, Pextra_ty p2) -> compare_extra p1 p2
  | (Pident _, (Pdot _ | Papply _ | Pextra_ty _))
  | (Pdot _, (Papply _ | Pextra_ty _))
  | (Papply _, Pextra_ty _)
    -> -1
  | ((Pextra_ty _ | Papply _ | Pdot _), Pident _)
  | ((Pextra_ty _ | Papply _) , Pdot _)
  | (Pextra_ty _, Papply _)
    -> 1
and compare_extra p1 p2 =
  if p1 == p2 then 0
  else match (p1, p2) with
    (Pcstr_ty(p1, s1), Pcstr_ty(p2, s2)) ->
      let h = compare p1 p2 in
      if h <> 0 then h else String.compare s1 s2
  | (Pext_ty p1, Pext_ty p2) -> compare p1 p2
  | (Pcls_ty p1, Pcls_ty p2) -> compare p1 p2
  | (Pcstr_ty _, (Pext_ty _ | Pcls_ty _))
  | (Pext_ty _, Pcls_ty _)
    -> -1
  | ((Pcls_ty _ | Pext_ty _), Pcstr_ty _)
  | (Pcls_ty _, Pext_ty _)
    -> 1

let rec find_free_opt ids = function
    Pident id -> List.find_opt (Ident.same id) ids
  | Pdot(p, _) -> find_free_opt ids p
  | Papply(p1, p2) -> begin
      match find_free_opt ids p1 with
      | None -> find_free_opt ids p2
      | Some _ as res -> res
    end
  | Pextra_ty p -> find_free_opt ids (path_of_extra_ty p)

let exists_free ids p =
  match find_free_opt ids p with
  | None -> false
  | _ -> true

let rec scope = function
    Pident id -> Ident.scope id
  | Pdot(p, _) -> scope p
  | Papply(p1, p2) -> Int.max (scope p1) (scope p2)
  | Pextra_ty p -> scope (path_of_extra_ty p)

let kfalse _ = false

let rec name ?(paren=kfalse) = function
    Pident id -> Ident.name id
  | Pdot(p, s) ->
      name ~paren p ^ if paren s then ".( " ^ s ^ " )" else "." ^ s
  | Papply(p1, p2) -> name ~paren p1 ^ "(" ^ name ~paren p2 ^ ")"
  | Pextra_ty p ->
      match p with
        Pcstr_ty(p, s) ->
          name ~paren p ^ if paren s then ".( " ^ s ^ " )" else "." ^ s
      | Pext_ty p | Pcls_ty p -> name ~paren p


let rec print ppf = function
  | Pident id -> Ident.print_with_scope ppf id
  | Pdot(p, s) -> Format.fprintf ppf "%a.%s" print p s
  | Papply(p1, p2) -> Format.fprintf ppf "%a(%a)" print p1 print p2
  | Pextra_ty p ->
      match p with
        Pcstr_ty(p, s) -> Format.fprintf ppf "%a.%s" print p s
      | Pext_ty p | Pcls_ty p -> print ppf p

let rec head = function
    Pident id -> id
  | Pdot(p, _) -> head p
  | Papply _ -> assert false
  | Pextra_ty p -> head (path_of_extra_ty p)

let flatten =
  let rec flatten acc = function
    | Pident id -> `Ok (id, acc)
    | Pdot (p, s) -> flatten (s :: acc) p
    | Papply _ -> `Contains_apply
    | Pextra_ty p -> begin
        match p with
          Pcstr_ty(p, s) -> flatten (s :: acc) p
        | Pext_ty p | Pcls_ty p -> flatten acc p
      end
  in
  fun t -> flatten [] t

let heads p =
  let rec heads p acc = match p with
    | Pident id -> id :: acc
    | Pdot (p, _) -> heads p acc
    | Papply(p1, p2) ->
        heads p1 (heads p2 acc)
    | Pextra_ty p -> heads (path_of_extra_ty p) acc
  in heads p []

let rec last = function
  | Pident id -> Ident.name id
  | Pdot(_, s) -> s
  | Papply(_, p) -> last p
  | Pextra_ty p ->
      match p with
        Pcstr_ty(_, s) -> s
      | Pext_ty p | Pcls_ty p -> last p

let is_constructor_typath p =
  match p with
  | Pident _ | Pdot _ | Papply _ -> false
  | Pextra_ty _ -> true

module T = struct
  type nonrec t = t
  let compare = compare
end
module Set = Set.Make(T)
module Map = Map.Make(T)
