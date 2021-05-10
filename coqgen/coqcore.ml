(**************************************************************************)
(*                                                                        *)
(*                             OCaml in Coq                               *)
(*                                                                        *)
(**************************************************************************)

open Misc
open Types
open Btype

module Names = Stdlib.String.Set

type error = Not_allowed of string

exception Error of Location.t * error

let not_allowed ?(loc = Location.none) s =
  raise (Error (loc, Not_allowed s))

type coq_sort = Type | Set | Prop

type coq_term =
    CTid of string
  | CTapp of coq_term * coq_term list
  | CTabs of string * coq_term option * coq_term
  | CTsort of coq_sort
  | CTtuple of coq_term list
  | CTprod of string * coq_term option * coq_term

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
      ce_type: type_expr;
      ce_vars: type_expr list;
      ce_def: coq_term option;
    }

let stdlib = Path.Pident (Ident.create_persistent "Stdlib!")
let stdlib_ref = Path.Pdot (stdlib, "ref")
let newgenconstr p tl = newgenty (Tconstr (p, tl, ref Mnil))
let newgenarrow t1 t2 = newgenty (Tarrow (Nolabel, t1, t2, Cok))

let init_term_map =
  let int_to_int = newgenarrow Predef.type_int Predef.type_int in
  let int_to_int_to_int = newgenarrow Predef.type_int int_to_int in
  List.fold_left
    (fun map (lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) stdlib lid in
      Path.Map.add path desc map)
    Path.Map.empty
    [
     (["ref"],
      let tv = newgenvar () in
      {ce_name = "newref";
       ce_type = newgenarrow tv (newgenconstr stdlib_ref [tv]);
       ce_vars = [tv];
       ce_def = None});
     (["!"],
      let tv = newgenvar () in
      {ce_name = "getref";
       ce_type = newgenarrow (newgenconstr stdlib_ref [tv]) tv;
       ce_vars = [tv];
       ce_def = None});
     ([":="],
      let tv = newgenvar () in
      {ce_name = "setref";
       ce_type = newgenarrow (newgenconstr stdlib_ref [tv])
                             (newgenarrow tv Predef.type_unit);
       ce_vars = [tv];
       ce_def = None});
     (["+"],
      {ce_name = "Int63.add";
       ce_type = int_to_int_to_int;
       ce_vars = [];
       ce_def = None});
     (["-"],
      {ce_name = "Int63.sub";
       ce_type = int_to_int_to_int;
       ce_vars = [];
       ce_def = None});
     (["*"],
      {ce_name = "Int63.mul";
       ce_type = int_to_int_to_int;
       ce_vars = [];
       ce_def = None});
     (["/"],
      {ce_name = "Int63.div";
       ce_type = int_to_int_to_int;
       ce_vars = [];
       ce_def = None});
     (["mod"],
      {ce_name = "Int63.mod";
       ce_type = int_to_int_to_int;
       ce_vars = [];
       ce_def = None});
     (["~-"],
      {ce_name = "Int63.opp";
       ce_type = int_to_int;
       ce_vars = [];
       ce_def = None});
   ]

let type_map = ref (Path.Map.empty : coq_type_desc Path.Map.t)
let term_map = ref (Path.Map.empty : coq_term_desc Path.Map.t)

let get_used_top_names =
  let used_top_names = ref Names.empty in
  let last_type_map = ref !type_map in
  let last_term_map = ref !term_map in
  fun () ->
    let tm = !type_map and em = !term_map in
    if tm != !last_type_map || em != !last_term_map then begin
      let names =
        Path.Map.fold (fun _ td -> Names.add td.ct_name) tm Names.empty in
      let names =
        Path.Map.fold (fun _ td -> Names.add td.ce_name) em names in
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
  Names.mem s (get_used_top_names ()) ||
  TypeMap.exists (fun _ name -> name = s) vars

let fresh_var_name vars name =
  fresh_name ?name (used_var_name vars)

let rec transl_type ~loc (vars : string TypeMap.t) visited ty =
  let ty = repr ty in
  if TypeSet.mem ty visited then not_allowed ~loc "recursive types" else
  let visited = TypeSet.add ty visited in
  let transl_rec = transl_type ~loc vars visited in
  match ty.desc with
  | Tvar _ | Tunivar _ ->
      CTid (TypeMap.find ty vars)
  | Tarrow (Nolabel, t1, t2, _) ->
      CTapp (CTid "->", [transl_rec t1;
                         CTapp (CTid "M", [transl_rec t2])])
  | Tarrow _ ->
      not_allowed ~loc "labels"
  | Ttuple tl ->
      CTtuple (List.map transl_rec tl)
  | Tconstr (p, tl, _) ->
      let desc = Path.Map.find p !type_map in
      CTapp (CTid desc.ct_name, List.map transl_rec tl)
  | Tobject _ | Tfield _ | Tnil ->
      not_allowed ~loc "object types"
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
          vars vl
      in
      let ct1 = transl_type ~loc vars visited t1 in
      List.fold_right (fun tv ct -> CTprod (TypeMap.find tv vars, None, ct))
        vl ct1
  | Tpackage _ ->
      not_allowed ~loc "first class modules"
  | Tlink _ | Tsubst _ ->
      assert false

let is_alpha name =
  name <> "" &&
  match name.[0] with
    'a'..'z' | 'A'..'Z' -> true
  | _ -> false

let rec name_of_path path =
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
  ignore (path, td)

let find_instantiation ~loc env edesc ty =
  let open Ctype in
  let ty0, vars =
    let ty1 = newgenty (Ttuple (edesc.ce_type :: edesc.ce_vars)) in
    match (generic_instance ty1).desc with
      Ttuple (ty0 :: vars) -> ty0, vars
    | _ -> assert false
  in
  (try unify env ty ty0
   with Unify _ -> not_allowed ~loc ("Type for " ^ edesc.ce_name));
  vars
  
let rec transl_exp ~(tvars : string TypeMap.t) ~(vars : coq_term_desc Ident.tbl)
    e =
  let open Typedtree in
  let loc = e.exp_loc in
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
      let desc =
        try match path with
        | Path.Pident id -> Ident.find_same id vars
        | _ -> raise Not_found
        with Not_found ->
          try Path.Map.find path !term_map
          with Not_found ->
            not_allowed ~loc ("Identifier " ^ Path.name path)
      in
      let ivars = find_instantiation ~loc e.exp_env desc e.exp_type in
      let f = CTid desc.ce_name in
      if ivars = [] then f else
      CTapp (f, List.map (transl_type ~loc tvars TypeSet.empty) ivars)
  | _ ->
      ignore transl_exp;
      not_allowed ~loc "This kind of term"
          
let transl_implementation modname st =
  ignore (modname, st)

open Format

let priority_level = function
  | CTid _ -> 10
  | CTapp (CTid "->", [_;_]) -> 2
  | CTapp (CTid "*", [_;_]) -> 3
  | CTapp _ -> 4
  | CTabs _ -> 0
  | CTsort _ -> 10
  | CTtuple _ -> 10
  | CTprod _ -> 10

let string_of_sort = function
  | Type -> "Type"
  | Set -> "Set"
  | Prop -> "Prop"

let rec print_type_rec lv ppf ty =
  if lv > priority_level ty then fprintf ppf "(%a)" (print_type_rec 0) ty else
  match ty with
  | CTid s -> pp_print_string ppf s
  | CTapp (CTid "->", [t1; t2]) ->
      fprintf ppf "@[%a ->@ %a@]" (print_type_rec 3) t1 (print_type_rec 2) t2
  | CTapp (CTid "*", [t1; t2]) ->
      fprintf ppf "@[%a ->@ %a@]" (print_type_rec 3) t1 (print_type_rec 4) t2
  | CTapp (f, args) ->
      fprintf ppf "@[<2>%a@ %a]" (print_type_rec 4) f
        (pp_print_list ~pp_sep:pp_print_space (print_type_rec 5)) args
  | CTabs (x, ot, t1) ->
      fprintf ppf "@[<hov2>@[<hov2}fun@ %s%a@ =>@]@ %a@]"
        x print_type_ann ot (print_type_rec 0) t1
  | CTsort k -> pp_print_string ppf (string_of_sort k)
  | CTtuple tl ->
      fprintf ppf "(@[%a)@]"
        (pp_print_list (print_type_rec 1)
           ~pp_sep:(fun ppf () -> fprintf ppf ",@ "))
        tl
  | CTprod (x, ot, t1) ->
      fprintf ppf "@[<hov2>@[<hov2>forall@ %s%a,]@ %a@]"
        x print_type_ann ot (print_type_rec 0) t1

and print_type_ann ppf = function
  | None -> ()
  | Some t -> fprintf ppf "@ : %a" (print_type_rec 0) t

let emit_gallina modname ppf ct = ignore (modname, ppf, ct)

let report_error ppf = function
  | Not_allowed s ->
      Format.fprintf ppf "%s not allowed for Coq translation." s

let () =
  Location.register_error_of_exn
    (function
      | Error (loc, err) ->
        Some (Location.error_of_printer ~loc report_error err)
      | _ ->
        None
    )
