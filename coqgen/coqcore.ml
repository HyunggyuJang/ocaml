(**************************************************************************)
(*                                                                        *)
(*                             OCaml in Coq                               *)
(*                                                                        *)
(**************************************************************************)

open Misc
open Types

module Names = Stlib.String.Set

type error = Not_allowed of string

exception Error of Location.t * error

let not_allowed ?(loc = Location.none) s =
  raise (Error (loc, Not_allowed s))

type coq_kind = Type | Set | Prop

type coq_term =
    CTid of string
  | CTapp of coq_term * coq_term list
  | CTabs of string * coq_term option * coq_term
  | CTkind of coq_kind
  | CTtuple of coq_term list
  | CTprod of string * coq_term_option * coq_term

type coq_def_kind =
  | CT_def of coq_term
  | CT_ind of (string * coq_term) list

type coq_type_desc =
    { ct_name: string;
      ct_args: string list;
      ct_def: coq_def_kind;
    }

type coq_term_desc =
    { ce_name: string;
      ce_def: coq_term;
    }

let type_map = ref (Path.Map.empty : coq_type_desc Path.Map.t)
let term_map = ref (Path.Map.empty : coq_term_desc Path.Map.t)

let get_used_top_names =
  let used_top_names = ref Name.empty in
  let last_type_map = ref !type_map in
  let last_term_map = ref !term_map in
  fun () ->
    let tm = !type_map and em = !term_map in
    if tm != !last_type_map || em != last_term_map then
      let names =
        Path.Map.fold (fun _ td -> Names.add td.name) tm Names.empty in
      let names =
        Path.Map.fold (fun _ td -> Names.add td.name) em names in
      used_top_names := names;
      last_type_map := tm;
      last_term_map := em;
    end;
    !used_top_names

let fresh_name ?(name = "x") (used : string -> bool) =
  if not (used name) then name else
  let rec search n =
    let name_n = name ^ "_" ^ string_of_int n in
    if not (used name_n) then name_n else search (n+1)
  in search 1

let used_var_name vars s =
  Path.Map.exists (fun _ td -> td.name = s) !type_map ||
  TypeMap.exists (fun _ name -> name = s) vars

let fresh_var_name vars name =
  fresh_name ?name (used_var_name vars)

let rec transl_type loc (vars : string TypeMap.t) visited =
  let ty = repr ty in
  if TypeSet.mem ty visited then not_allowed ~loc "recursive types" else
  let visited = TypeSet.add ty visited in
  let transl_rec = transl_type loc vars visited in
  match ty.desc with
  | Tvar _ | Tunivar _ ->
      CTid (TypeMap.find ty vars)
  | Tarrow (NoLabel, t1, t2, _) ->
      CTapp (CTid "->", [transl_rec t1; transl_rec t2])
  | Tarrow _ ->
      not_allowed ~loc "labels"
  | Ttuple tl ->
      CTtuple (List.map transl_rec tl)
  | Tconstr (p, tyl, _) ->
      let desc = Path.Map.find p !type_map in
      CTapp (CTid desc.name, List.map transl_rec tl)
  | Tobject _ | Tfield _ | Tnil ->
      not_allowed ~loc "object types"
  | Tlink _ ->
      assert false
  | Tvariant _ ->
      not_allowed ~loc "polymorphic variants"
  | Tpoly (t1, vl) ->
      let vl = List.map repr vl in
      let vars =
        List.fold_left
          begin fun vars tv ->
            match tv.desc with
            | Tunivar name -> TypeMap.add tv (fresh_var_name vars name) vars
            | _ -> assert false
          end
          vl
      in
      let ct1 = transl_type vars visited t1 in
      List.fold_right (fun tv ct -> CTprod (TypeMap.find tv vars, None, ct))
        vl ct1
  | Tpackage _ ->
      not_allowed ~loc "first class modules"

let is_alpha name =
  name <> "" &&
  match name.[0] with
    'a'..'z' | 'A'..'Z' -> true
  | _ -> false

let name_of_path path =
  let open Path in
  match path with
    Pident id ->
      let name = Ident.name id in
      if is_alpha name then "ml_" ^ name else
      if name = "" then "ml_unnamed" else name
  | Pdot (p, s) ->
      let pre = name_of_path p in
      if is_alpha s then pre ^ "_" ^ s else pre ^ "_unnamed"
  | Papply _ ->
      not_allowed "functor applications"

let transl_type_decl path td =
  

let report_error ppf = function
  | Not_allowed s ->
      Format.fprintf ~loc "%s not allowed for Coq translation." s

let () =
  Location.register_error_of_exn
    (function
      | Error (loc, err) ->
        Some (Location.error_of_printer ~loc report_error err)
      | _ ->
        None
    )
