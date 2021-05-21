(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Jacques Garrigue, Nagoya University                        *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Misc
open Asttypes
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
  | CTcstr of string
  | CTapp of coq_term * coq_term list
  | CTabs of string * coq_term option * coq_term
  | CTsort of coq_sort
  | CTprod of string option * coq_term * coq_term
  | CTmatch of
      coq_term * (string * coq_term) option * (coq_term * coq_term) list
  | CTann of coq_term * coq_term
  | CTlet of string * coq_term option * coq_term * coq_term
  | CTif of coq_term * coq_term * coq_term

let ctid s = CTid s
let ctcstr s = CTcstr s
let ctapp ct args = if args = [] then ct else CTapp (ct, args)
let ctRet ct = CTapp (CTid "Ret", [ct])
let ctBind m f = CTapp (CTid "Bind", [m; f])
let ctpair a b = CTapp (CTcstr "pair", [a;b])

let ml_type = "ml_type"
let ml_tid = CTid ml_type
let coq_tid = CTid "coq_type"

type coq_def_kind =
  | CT_def of coq_term
  | CT_ind of (string * coq_term) list
  | CT_abs

type coq_type_desc =
    { ct_name: string;
      ct_args: string list;
      ct_def: coq_def_kind;
      ct_constrs: (string * string) list;
      ct_compare: coq_term option;
    }

type coq_term_desc =
    { ce_name: string;
      ce_type: type_expr;
      ce_vars: type_expr list;
      ce_rec: rec_flag;
      ce_purary: int; (* pure arity: number of application before monad *)
    }

type coq_env =
    { type_map: coq_type_desc Path.Map.t;
      term_map: coq_term_desc Path.Map.t;
      tvar_map: string TypeMap.t;
      top_exec: string list;
      coq_names: Names.t;
    }

type term_props =
    { pterm: coq_term; prec: rec_flag; pary: int }

let empty_vars =
  { type_map = Path.Map.empty;
    term_map = Path.Map.empty;
    tvar_map = TypeMap.empty;
    top_exec = [];
    coq_names = Names.empty;
  }

let add_type path td vars =
  { vars with
    type_map = Path.Map.add path td vars.type_map;
    coq_names = Names.add td.ct_name vars.coq_names }

let add_term ?(toplevel = false) path td vars =
  let td, top_exec =
    if toplevel && td.ce_purary = 0 then
      td (*{td with ce_purary = 1}*), td.ce_name :: vars.top_exec
    else td, vars.top_exec
  in
  { vars with
    term_map = Path.Map.add path td vars.term_map;
    top_exec = top_exec;
    coq_names = Names.add td.ce_name vars.coq_names }

let add_tvar tv name vars =
  { vars with
    tvar_map = TypeMap.add tv name vars.tvar_map;
    coq_names = Names.add name vars.coq_names }

let add_reserved name vars =
  { vars with coq_names = Names.add name vars.coq_names }

let stdlib = Path.Pident (Ident.create_persistent "Stdlib")
let coqgen = Path.Pident (Ident.create_persistent "coqgen")
let stdlib_ref = Path.Pdot (stdlib, "ref")
let newgenconstr p tl = newgenty (Tconstr (p, tl, ref Mnil))
let newgenarrow t1 t2 = newgenty (Tarrow (Nolabel, t1, t2, Cok))

let xy = [CTid"x"; CTid"y"]

let init_type_map vars =
  List.fold_left
    (fun map (rt, lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) rt lid in
      add_type path desc map)
    vars
  [
   (stdlib, ["ref"],
    {ct_name = "ml_ref"; ct_args = ["a"]; ct_def = CT_abs; ct_constrs = [];
     ct_compare = Some (
     ctBind (ctapp (CTid"getref") [CTid"T1"; CTid"x"])
       (CTabs ("x", None, ctBind (ctapp (CTid"getref") [CTid"T1"; CTid"y"])
                 (CTabs ("y", None, ctapp (CTid"compare_rec")
                           [CTid"T1";CTid"h";CTid"x";CTid"y"])))))
   });
   (Predef.path_int, [],
    {ct_name = "ml_int"; ct_args = []; ct_def = CT_def(CTid "Int63.int");
     ct_constrs = [];
     ct_compare = Some (ctRet (CTapp (CTid"Int63.compare", xy)))});
   (Predef.path_unit, [],
    {ct_name = "ml_unit"; ct_args = []; ct_def = CT_def(CTid "unit");
     ct_constrs = ["()", "tt"];
     ct_compare = Some (ctRet (CTid "Eq"))});
   (Predef.path_bool, [],
    {ct_name = "ml_bool"; ct_args = []; ct_def = CT_def(CTid "bool");
     ct_constrs = List.map (fun x -> (x,x)) ["true"; "false"];
     ct_compare = Some (ctRet (CTapp (CTid"Bool.compare", xy)))});
   (Predef.path_list, [],
    {ct_name = "ml_list"; ct_args = ["a"];
     ct_constrs = [("[]", "@nil"); ("::", "@cons")];
     ct_def = CT_def (CTapp (CTid "list", [CTid "a"]));
     ct_compare = None;
     (*Some (
       CTmatch (CTpair(CTid"x",CTid"y"),[
       (CTpair*)
   });
   (coqgen, ["arrow"],
    {ct_name = "ml_arrow"; ct_args = ["a"; "b"]; ct_constrs = [];
     ct_def = CT_def (CTprod (None, CTid"a", CTapp(CTid"M", [CTid"b"])));
     ct_compare = None});
  ]

let init_term_map vars =
  let int_to_int = newgenarrow Predef.type_int Predef.type_int in
  let int_to_int_to_int = newgenarrow Predef.type_int int_to_int in
  List.fold_left
    (fun map (lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) stdlib lid in
      add_term path desc map)
    vars (
  [
   (["*h"],
    {ce_name = "h";
     ce_type = Predef.type_int;
     ce_vars = [];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   (["ref"],
    let tv = newgenvar () in
    {ce_name = "newref";
     ce_type = newgenarrow tv (newgenconstr stdlib_ref [tv]);
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   (["!"],
    let tv = newgenvar () in
    {ce_name = "getref";
     ce_type = newgenarrow (newgenconstr stdlib_ref [tv]) tv;
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   ([":="],
    let tv = newgenvar () in
    {ce_name = "setref";
     ce_type = newgenarrow (newgenconstr stdlib_ref [tv])
       (newgenarrow tv Predef.type_unit);
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 2});
  ] @
  List.map
    (fun (ml, coq) ->
      [ml],
      {ce_name = coq;
       ce_type = int_to_int_to_int;
       ce_vars = [];
       ce_rec = Nonrecursive;
       ce_purary = 3})
    [("+", "Int63.add"); ("-", "Int63.sub"); ("*", "Int63.mul");
     ("/", "Int63.div"); ("mod", "Int63.mod")]
  @ [
    (["~-"],
     {ce_name = "Int63.opp";
      ce_type = int_to_int;
      ce_vars = [];
      ce_rec = Nonrecursive;
      ce_purary = 2})
  ] @
  List.map
    (fun (ml, coq) ->
      [ml],
      let tv = newgenvar () in
      {ce_name = coq;
       ce_vars = [tv];
       ce_type = newgenarrow tv (newgenarrow tv Predef.type_bool);
       ce_rec = Recursive;
       ce_purary = 2})
    [("=", "ml_eq"); ("<>", "ml_ne");
     ("<", "ml_lt"); (">", "ml_gt");
     ("<=", "ml_le"); (">=", "ml_ge")]
 )

let init_reserved = ["fix"; "Definition"; "Fixpoint"; "Inductive"]

let init_vars =
  init_type_map (
  init_term_map {empty_vars with coq_names = Names.of_list init_reserved}
)

let fresh_name ~vars name =
  if not (Names.mem name vars.coq_names) then name else
  let rec search n =
    let name_n = name ^ "_" ^ string_of_int n in
    if not (Names.mem name_n vars.coq_names) then name_n else search (n+1)
  in search 1

let fresh_opt_name ?(name = "T") vars =
  fresh_name ~vars name

let fresh_var_name ~vars name =
  fresh_opt_name ?name vars

let may_app f o x =
  match o with
    None -> x
  | Some y -> f y x

let rec coq_vars = function
  | CTid x -> Names.singleton x
  | CTcstr _ -> Names.empty
  | CTapp (ct, ctl) ->
      List.fold_left Names.union (coq_vars ct) (List.map coq_vars ctl)
  | CTabs (x, cto, ct) ->
      Names.union (Names.remove x (coq_vars ct)) (coq_vars_opt cto)
  | CTsort _ -> Names.empty
  | CTprod (ox, ct1, ct2) ->
      let vars = may_app Names.remove ox (coq_vars ct2) in
      Names.union vars (coq_vars ct1)
  | CTmatch (ct, oret, cases) ->
      let case_ret =
        Option.to_list (Option.map (fun (v,ct) -> CTid v, ct) oret) in
      let cases_vars (lhs,rhs) = Names.diff (coq_vars rhs) (coq_vars lhs) in
      List.fold_left Names.union (coq_vars ct)
        (List.map cases_vars (case_ret @ cases))
  | CTann (ct1, ct2) ->
      Names.union (coq_vars ct1) (coq_vars ct2)
  | CTlet (x, cto, ct1, ct2) ->
      Names.union (coq_vars_opt cto)
        (Names.union (coq_vars ct1) (Names.remove x (coq_vars ct2)))
  | CTif (ct1, ct2, ct3) ->
      Names.union (coq_vars ct1) (Names.union (coq_vars ct2) (coq_vars ct3))

and coq_vars_opt = function
  | None -> Names.empty
  | Some ct -> coq_vars ct

(* XXX should handle capture *)
let rec coq_term_subst subs = function
  | CTid x as ct ->
      if Vars.mem x subs then Vars.find x subs else ct
  | CTcstr _ as ct ->
      ct
  | CTapp (x, l) ->
      CTapp (coq_term_subst subs x, List.map (coq_term_subst subs) l)
  | CTabs (x, t, b) ->
      let subs' =
        if Vars.mem x subs then Vars.remove x subs else subs in
      CTabs (x, Option.map (coq_term_subst subs) t,
             coq_term_subst subs' b)
  | CTsort _ as ct -> ct
  | CTprod (ox, t, b) ->
      let subs' = may_app Vars.remove ox subs in
      CTprod (ox, coq_term_subst subs t, coq_term_subst subs' b)
  | CTmatch (ct, oret, cases) ->
      let subs_ret (v, ct) = v, coq_term_subst (Vars.remove v subs) ct in
      let subs_case (lhs, rhs) =
        let subs' = Names.fold Vars.remove (coq_vars lhs) subs in
        (lhs, coq_term_subst subs' rhs)
      in
      CTmatch (coq_term_subst subs ct, Option.map subs_ret oret,
               List.map subs_case cases)
  | CTann (ct1, ct2) ->
      CTann (coq_term_subst subs ct1, coq_term_subst subs ct2)
  | CTlet (x, cto, ct1, ct2) ->
      let subs' =
        if Vars.mem x subs then Vars.remove x subs else subs in
      CTlet (x, Option.map (coq_term_subst subs) cto,
             coq_term_subst subs ct1, coq_term_subst subs' ct2)
  | CTif (ct1, ct2, ct3) ->
      CTif (coq_term_subst subs ct1, coq_term_subst subs ct2,
            coq_term_subst subs ct3)

let make_tuple_type ctl =
  List.fold_left
    (fun ct ct' ->
      if ct = CTid "unit" then ct' else CTapp (CTid "ml_pair", [ct; ct']))
    (CTid "unit") ctl

let rec transl_type ~loc ~vars visited ty =
  let ty = repr ty in
  if TypeSet.mem ty visited then not_allowed ~loc "recursive types" else
  let visited = TypeSet.add ty visited in
  let transl_rec = transl_type ~loc ~vars visited in
  match ty.desc with
  | Tvar _ | Tunivar _ ->
      CTid (TypeMap.find ty vars.tvar_map)
  | Tarrow (Nolabel, t1, t2, _) ->
      CTapp (CTid "ml_arrow", [transl_rec t1; transl_rec t2])
  | Tarrow _ ->
      not_allowed ~loc "labels"
  | Ttuple tl ->
      make_tuple_type (List.map transl_rec tl)
  | Tconstr (p, tl, _) ->
      let desc = Path.Map.find p vars.type_map in
      ctapp (CTid desc.ct_name) (List.map transl_rec tl)
  | Tnil ->
      CTid "ml_unit"
  | Tobject _ | Tfield _ ->
      not_allowed ~loc "object types"
  | Tvariant _ ->
      not_allowed ~loc "polymorphic variants"
  | Tpoly (t1, vl) ->
      let vl = List.map repr vl in
      let vars =
        List.fold_left
          begin fun vars tv ->
            match tv.desc with
            | Tunivar name -> add_tvar tv (fresh_var_name ~vars name) vars
            | _ -> assert false
          end
          vars vl
      in
      let ct1 = transl_type ~loc ~vars visited t1 in
      List.fold_right
        (fun tv ct -> CTprod (Some (TypeMap.find tv vars.tvar_map), ml_tid, ct))
        vl ct1
  | Tpackage _ ->
      not_allowed ~loc "first class modules"
  | Tlink _ | Tsubst _ ->
      assert false

let transl_type ~loc ~vars = transl_type ~loc ~vars TypeSet.empty

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
  if edesc.ce_vars = [] then [] else
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

let close_type ty =
  let vars = Ctype.free_variables ty in
  List.iter
    (fun ty ->
      if ty.level <> Btype.generic_level then
        Btype.link_type ty (Btype.newty2 ty.level Tnil))
    vars

open Typedtree

let vars_names tbl =
  Ident.fold_name (fun _ {ce_name} l -> ce_name :: l) tbl []

let make_tuple ctl =
  List.fold_left
    (fun ct ct' ->
      if ct = CTid "tt" then ct' else CTapp (CTid"pair", [ct; ct']))
    (CTid "tt") ctl

let name_tuple names =
  let ctl = List.map ctid names in
  make_tuple ctl

let enter_free_variables ~vars ty =
  (*close_type ty;*)
  let fvars = Ctype.free_variables ty in
  let fvars =
    List.filter (fun ty -> not (TypeMap.mem ty vars.tvar_map)) fvars in
  let (fvar_names, vars) =
    List.fold_left
      (fun (names, vars) tv -> match tv.desc with
      | Tvar name ->
          let v = fresh_var_name ~vars name in
          v :: names, add_tvar tv v vars
      | _ -> assert false)
      ([],vars) fvars
  in
  (*List.iter (Format.eprintf "fvar=%a@." Printtyp.raw_type_expr) fvars;*)
  fvars, List.rev fvar_names, vars

let refresh_tvars vars =
  { vars with tvar_map =
    TypeMap.fold (fun ty -> TypeMap.add (repr ty)) vars.tvar_map TypeMap.empty }

let rec fun_arity e =
  match e.exp_desc with
  | Texp_function
    {cases=[{c_lhs={pat_desc=(Tpat_var _|Tpat_any)};c_guard=None;c_rhs}]} ->
      1 + fun_arity c_rhs
  | Texp_function _ -> 1
  | _ -> 0

let rec shrink_purary_val ~vars ~args p1 p2 ct =
  if p1 <= 1 then ctapp ct (List.rev args) else
  let x = fresh_name ~vars "x" in
  let ct1 =
    CTabs (x, None,
           shrink_purary_val ~vars:(add_reserved x vars) ~args:(CTid x :: args)
             (p1-1) (p2-1) ct)
  in
  if p2 <= 0 then ctRet ct1 else ct1

let rec shrink_purary_rec ~vars p1 p2 ct =
  assert (p2 <= p1);
  if p1 <= 0 || p1 = p2 then ct else
  let ct2 =
    match ct with
    | CTabs (x, t, ct1) ->
        let vars = add_reserved x vars in
        CTabs (x, t, shrink_purary_rec ~vars (p1-1) (p2-1) ct1)
    | _ ->
        shrink_purary_val ~vars ~args:[] p1 p2 ct
  in
  if p2 <= 0 then ctRet ct2 else ct2

let shrink_purary ~vars pt p2 =
  if pt.pary = p2 then pt else
  {pterm = shrink_purary_rec ~vars pt.pary p2 pt.pterm;
   prec = pt.prec; pary = p2}

let nullary ~vars pt =
  shrink_purary ~vars pt 0

let rec cut n l =
  if n <= 0 then ([], l) else
  match l with
  | [] -> invalid_arg "cut"
  | a :: l -> let (l1, l2) = cut (n-1) l in (a::l1, l2)

let or_rec r1 r2 =
  match r1, r2 with
  | Nonrecursive, Nonrecursive -> Nonrecursive
  | _ -> Recursive

let rec insert_guard ct =
  match ct with
    CTabs (v, Some cty, body) when not (Names.mem "h" (coq_vars cty)) ->
      CTabs (v, Some cty, insert_guard body)
  | CTabs (v, None, body) ->
      CTabs (v, None, insert_guard body)
  | CTann (ct, cty) when not (Names.mem "h" (coq_vars cty)) ->
      CTann (insert_guard ct, cty)
  | _ ->
      CTmatch (CTid "h", None,
               [(CTapp(CTid"S",[CTid"h"]),ct); (CTid"_", CTid"Fail")])

let string_of_constant ~loc = function
  | Const_int x ->
      let s = string_of_int x ^ "%int63" in
      if x < 0 then "("^s^")" else s
  | Const_char c ->
      let s = Char.escaped c in
      let s =
        if String.length s = 1 then s else
        Printf.sprintf "%03d" (Char.code c) in
      Printf.sprintf "\"%s\"%%ascii" s
  | Const_string (s, _, _) ->
      Printf.sprintf "\"%s\"%%string" s
  | _ ->
      not_allowed ~loc "This constant"

let find_constructor ~loc ~vars cd =
  let path, tl =
    match repr cd.cstr_res with
    | {desc = Tconstr (path, tl, _)} -> path, tl
    | _ -> assert false
  in
  try
    let ct = Path.Map.find path vars.type_map in
    List.assoc cd.cstr_name ct.ct_constrs, tl
  with Not_found ->
    not_allowed ~loc
      ("The constructor " ^ cd.cstr_name ^ " of type " ^ Path.name path)

let rec transl_pat : type k. vars:_ -> k general_pattern -> _ =
  fun ~vars pat ->
  let loc = pat.pat_loc in
  match pat.pat_desc with
  | Tpat_any -> (CTid "_", vars)
  | Tpat_var (id, _) ->
      let name = fresh_name ~vars (Ident.name id) in
      let desc =
        { ce_name = name; ce_type = pat.pat_type;
          ce_vars = []; ce_rec = Nonrecursive; ce_purary = 1 } in
      let vars = add_term (Path.Pident id) desc vars in
      (CTid name, vars)
  | Tpat_constant cst ->
      (CTcstr (string_of_constant ~loc cst), vars)
  | Tpat_tuple [] ->
      (CTcstr "()", vars)
  | Tpat_tuple (pat1 :: patl) ->
      List.fold_left
        (fun (ctt, vars) pat ->
          let (ct, vars) = transl_pat ~vars pat in (ctpair ctt ct, vars))
        (transl_pat ~vars pat1) patl
  | Tpat_construct (_, cd, patl, _) ->
      let (ctl, vars) =
        List.fold_left
          (fun (ctl, vars) pat ->
            let (ct, vars) = transl_pat ~vars pat in
            (ct :: ctl, vars))
          ([],vars) patl
      in
      let name, tl = find_constructor ~loc ~vars cd in
      let args = List.map (fun _ -> CTid "_") tl @ List.rev ctl in
      (ctapp (CTcstr name) args, vars)
  | Tpat_value pat ->
      transl_pat ~vars (pat :> value general_pattern)
  | _ ->
      not_allowed ~loc "transl_pat : This pattern"

let is_primitive s =
  String.length s >= 2 && s.[0] = '@'

let transl_ident ~loc ~vars env desc ty =
  if desc.ce_purary = 0 then
    {pterm = CTid desc.ce_name; prec = Nonrecursive; pary = 1}
  else
  let snap = Btype.snapshot () in
  let ivars = find_instantiation ~loc env desc ty in
  (*List.iter (Format.eprintf "ivar=%a@." Printtyp.raw_type_expr) ivars;*)
  let vars = refresh_tvars vars in
  let f = CTid desc.ce_name in
  let args = List.map (transl_type ~loc ~vars) ivars in
  let args =
    if is_primitive desc.ce_name
    then List.map (fun x -> CTapp (coq_tid, [x])) args
    else args in
  Btype.backtrack snap;
  let args =
    if desc.ce_rec = Recursive then args @ [CTid"h"] else args in
  {pterm = ctapp f args; prec = desc.ce_rec; pary = desc.ce_purary}

let rec transl_exp ~vars e =
  let loc = e.exp_loc in
  close_type e.exp_type;
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
      let desc =
        try Path.Map.find path vars.term_map
        with Not_found ->
          not_allowed ~loc ("Identifier " ^ Path.name path)
      in
      transl_ident ~loc ~vars e.exp_env desc e.exp_type
  | Texp_constant (Const_int n) ->
      {pterm = CTid (string_of_int n ^ "%int63"); prec = Nonrecursive;
       pary = 1 }
  | Texp_let (Nonrecursive, vbl, body) ->
      let ctl =
        List.map (transl_binding ~vars ~rec_flag:Nonrecursive) vbl in
      let (id_descs, ctl) = List.split ctl in
      let names = List.map (fun (_,desc) -> desc.ce_name) id_descs in
      let vars =
        List.fold_right
          (fun (id, desc) vars ->
            match id with
            | Some id ->
                let desc =
                  if desc.ce_purary = 0 then {desc with ce_purary = 1}
                  else desc in
                add_term (Path.Pident id) desc vars
            | None -> vars)
          id_descs
          vars
      in
      let pbody = transl_exp ~vars body in
      let prec = List.fold_right (fun ct -> or_rec ct.prec) ctl pbody.prec in
      let pbody = {pbody with prec} in
      let pat = name_tuple names in
      let ct = make_tuple (List.map (fun ct -> ct.pterm) ctl) in
      begin match pat, id_descs with
      | CTid v, [(_, desc)] ->
          if desc.ce_purary = 0 then
            let pbody = nullary ~vars pbody in
            {pbody with pterm = ctBind ct (CTabs (v, None, pbody.pterm))}
          else
            {pbody with pterm = CTlet (v, None, ct, pbody.pterm)}
      | _ ->
          if List.exists (fun (_,desc) -> desc.ce_purary = 0) id_descs then
            let pbody = nullary ~vars pbody in
            let pbody =
              List.fold_right
                (fun (_,{ce_name; ce_purary}) pbody ->
                  if ce_purary <> 0 then pbody else
                  {pbody with pterm =
                   ctBind (CTid ce_name) (CTabs (ce_name, None, pbody.pterm))})
                id_descs pbody in
            let v = fresh_name ~vars "v" in
            {pbody with pterm =
             ctBind ct (CTabs (v, None,
                               CTmatch (CTid v, None, [pat, pbody.pterm])))}
          else
            {pbody with pterm = CTmatch (ct, None, [pat, pbody.pterm])}
      end
  | Texp_sequence (e1, e2) ->
      let ct1 = nullary ~vars (transl_exp ~vars e1) in
      let ct2 = nullary ~vars (transl_exp ~vars e2) in
      {pterm = ctBind ct1.pterm (CTabs ("_", None, ct2.pterm));
       prec = or_rec ct1.prec ct2.prec; pary = 0}
  | Texp_function
      {arg_label = Nolabel; param = _;
       cases = [{c_lhs = {pat_type; pat_loc} as pat;
                 c_rhs; c_guard = None}]} ->
      let (arg, vars) = transl_pat ~vars pat in
      let cty = transl_type ~loc:pat_loc ~vars pat_type in
      let cty = CTapp(coq_tid,[cty]) in
      let ct = transl_exp ~vars c_rhs in
      let ct =
        match ct.pterm with
          CTabs _ | CTann _ -> ct
        | pt ->
            if ct.pary >= 2 then ct else
            let cty = transl_type ~loc:c_rhs.exp_loc ~vars c_rhs.exp_type in
            let cty = CTapp (coq_tid,[cty]) in
            let cty = if ct.pary = 0 then CTapp (CTid"M", [cty]) else cty in
            {ct with pterm = CTann (pt, cty)}
      in
      let pterm =
        match arg with
          CTid v -> CTabs (v, Some cty, ct.pterm)
        | pat ->
            let v = fresh_name ~vars "v" in
            CTabs (v, Some cty, CTmatch (CTid v, None, [pat, ct.pterm]))
      in
      {pterm; prec  = ct.prec; pary  = ct.pary + 1}
  | Texp_apply (f, args)
    when List.for_all (function (Nolabel,Some _) -> true | _ -> false) args ->
      let args =
        List.map (function (_,Some arg) -> arg | _ -> assert false) args in
      let ct = transl_exp ~vars f in
      let ctl = List.map (transl_exp ~vars) args in
      let prec =
        if List.exists (fun ct -> ct.prec = Recursive) (ct :: ctl)
        then Recursive else Nonrecursive
      in
      let args, binds, vars =
        List.fold_right
          (fun ct (args, binds, vars) ->
            if ct.pary >= 1 then
              ((shrink_purary ~vars ct 1).pterm :: args, binds, vars)
            else
              let v = fresh_name ~vars "v" in
              (CTid v :: args, (v, ct.pterm) :: binds, add_reserved v vars))
          ctl ([],[],vars)
      in
      let ct =
        if ct.pary >= List.length args then
          {pterm = ctapp ct.pterm args; prec; pary = ct.pary - List.length args}
        else let args1, args2 = cut ct.pary args in
        let ct1 = ctapp ct.pterm args1 in
        {pterm =
         List.fold_left (fun ct1 arg -> CTapp (CTid"AppM", [ct1; arg]))
           ct1 args2;
         prec; pary = 0}
      in
      if binds = [] then ct else
      List.fold_left
        (fun ct (v,arg) ->
          {ct with pterm = ctBind arg (CTabs (v,None,ct.pterm))})
        (nullary ~vars ct) binds
  | Texp_construct (_, cd, []) ->
      let name, tl = find_constructor ~loc ~vars cd in
      let ce =
        {ce_name = name;
         ce_type = List.fold_right newgenarrow cd.cstr_args cd.cstr_res;
         ce_vars = tl;
         ce_rec = Nonrecursive;
         ce_purary = cd.cstr_arity + 1}
      in
      transl_ident ~loc ~vars e.exp_env ce e.exp_type
  | Texp_construct (lid, cd, args) ->
      let ty =
        List.fold_right (fun arg -> newgenarrow arg.exp_type) args e.exp_type
      in
      let constr =
        {e with exp_desc = Texp_construct (lid, cd, []); exp_type = ty} in
      let args = List.map (fun e -> (Nolabel, Some e)) args in
      let app = {e with exp_desc = Texp_apply (constr, args)} in
      begin match transl_exp ~vars app with
      | {pterm = CTapp (CTapp (f, args1), args2)} as ct ->
          {ct with pterm = CTapp (f, args1 @ args2)}
      | ct -> ct
      end
  | Texp_ifthenelse (be, e1, e2) ->
      let ct = transl_exp ~vars be
      and ct1 = transl_exp ~vars e1
      and ct2 =
        match e2 with
        | None    -> {pterm = CTid "tt"; prec = Nonrecursive; pary = 1}
        | Some e2 -> transl_exp ~vars e2
      in
      let prec = or_rec ct.prec (or_rec ct1.prec ct2.prec) in
      if ct.pary = 0 then
        let v = fresh_name ~vars "v" in
        let vars = add_reserved v vars in
        let ct1 = nullary ~vars ct1
        and ct2 = nullary ~vars ct2 in
        {pterm =
         ctBind ct.pterm (CTabs (v, None, CTif (CTid v, ct1.pterm, ct2.pterm)));
         pary = 0; prec}
      else
        let pary = min ct1.pary ct2.pary in
        let ct1 = shrink_purary ~vars ct1 pary
        and ct2 = shrink_purary ~vars ct2 pary in
        {pterm = CTif (ct.pterm, ct1.pterm, ct2.pterm); prec; pary}
  | Texp_match (e, cases, partial) ->
      let ct = transl_exp ~vars e in
      let ccases = List.map (transl_cases ~vars) cases in
      let lhs, ctl = List.split ccases in
      let prec =
        if List.exists (fun ct -> ct.prec = Recursive) (ct :: ctl)
        then Recursive else Nonrecursive
      in
      let pary =
        if partial = Partial then 0 else
        List.fold_left (fun pary ct -> min pary ct.pary) ct.pary ctl in
      let ctl =
        List.map2 (fun (_, vars) ct -> (shrink_purary ~vars ct pary).pterm)
          lhs ctl
      in
      let ccases = List.combine (List.map fst lhs) ctl in
      let ccases =
        if partial = Partial then ccases @ [CTid"_", CTid"Fail"] else ccases in
      let pterm =
        if ct.pary = 0 then
          let v = fresh_name ~vars "v" in
          ctBind ct.pterm (CTabs (v, None, CTmatch (CTid v, None, ccases)))
        else CTmatch (ct.pterm, None, ccases)
      in
      {pterm; prec; pary}
  | _ ->
      not_allowed ~loc "This kind of term"

and transl_cases ~vars case =
  Option.iter (fun e -> not_allowed ~loc:e.exp_loc "This guard") case.c_guard;
  let ct_lhs, vars = transl_pat ~vars case.c_lhs in
  let ct_rhs = transl_exp ~vars case.c_rhs in
  ((ct_lhs, vars), ct_rhs)

and transl_binding ~vars ~rec_flag vb =
  let name, id =
    match vb.vb_pat.pat_desc with
      Tpat_any -> "_", None
    | Tpat_var (id, _) -> fresh_name ~vars (Ident.name id), Some id
    | Tpat_construct (_, {cstr_name="()"}, [], _) -> "_", None
    | _ -> not_allowed ~loc:vb.vb_pat.pat_loc "This pattern"
  in
  let ty = vb.vb_expr.exp_type in
  (*Format.eprintf "exp_type=%a@." Printtyp.raw_type_expr ty;*)
  let fvars, fvar_names, vars = enter_free_variables ~vars ty in
  let desc =
    {ce_name = name; ce_type = ty; ce_vars = fvars;
     ce_rec = rec_flag; ce_purary = fun_arity vb.vb_expr}
  in
  let vars =
    match rec_flag, id with
    | Recursive, Some id -> add_term (Path.Pident id) desc vars
    | _ -> vars
  in
  let ct = transl_exp ~vars vb.vb_expr in
  let ct, desc, prec =
    match rec_flag with
    | Recursive ->
        let ct = shrink_purary ~vars ct desc.ce_purary in
        CTabs ("h", Some (CTid"nat"), insert_guard ct.pterm), desc,
        Nonrecursive
      (*
        let ct =
          if purary = desc.ce_purary then ct else
          let names = Names.of_list (vars_names vars) in
          shrink_purary ~vars purary 1 ct
        in
        let pat = vb.vb_pat in
        let loc = pat.pat_loc in
        let cty = transl_type ~loc tvars pat.pat_type in
        let _cty = CTapp (CTid "coq_type", [cty]) in
        let cty1, cty2 =
          match Btype.repr pat.pat_type with
            {desc = Tarrow (Nolabel, t1, t2, _)} ->
              transl_type ~loc tvars t1, transl_type ~loc tvars t2
          | _ -> CTid"_", CTid"_"
        in
        CTapp (CTid "Fix",
               [cty1; cty2; CTabs (desc.ce_name, None, ctRet ct)]),
        {desc with ce_purary = 0}
      *)
    | Nonrecursive ->
        ct.pterm, {desc with ce_purary = ct.pary}, ct.prec
  in
  let ct =
     List.fold_right (fun tv ct -> CTabs (tv, Some ml_tid, ct))
       fvar_names ct in
  ((id, desc), {pterm = ct; prec; pary = desc.ce_purary})

type vernacular =
  | CTdefinition of string * coq_term
  | CTfixpoint of string * coq_term
  | CTeval of coq_term
  | CTinductive of
      { name: string; args: (string * coq_term) list; kind: coq_term;
        cases: (string * (string * coq_term) list * coq_term) list }
  | CTverbatim of string

let apply_recursive rec_flag ct =
  if rec_flag = Nonrecursive then ct else
  coq_term_subst (Vars.add "h" (CTid"100000") Vars.empty) ct
  (* CTlet ("h", None, CTid"1000", ct) *)

let rec abstract_recursive ct =
  match ct with
  | CTabs (v, Some tid, ct) when tid = ml_tid ->
      CTabs (v, Some tid, abstract_recursive ct)
  | _ ->
      CTabs ("h", Some (CTid"nat"), ct)

let close_top ~vars ct =
  let fvars = coq_vars ct.pterm in
  let is_pure =
    ct.pary > 0 && Names.disjoint fvars (Names.of_list vars.top_exec) in
  if is_pure then ct.pterm else
  let ct = (nullary ~vars ct).pterm in
  let fvars =
    match vars.top_exec with [] -> fvars | v :: _ -> Names.add v fvars in
  let ct =
    List.fold_left
      (fun ct v ->
        if not (Names.mem v fvars) then ct else
        ctBind (CTabs ("_", None, CTid v)) (CTabs (v, None, ct)))
      ct vars.top_exec in
  ctapp ct [CTid "empty_env"]

let rec transl_structure ~vars = function
    [] -> ([], vars)
  | it :: rem -> match it.str_desc with
    | Tstr_eval (e, _) ->
        Ctype.unify_var e.exp_env (Ctype.newvar ()) e.exp_type;
        close_type e.exp_type;
        let pt = transl_exp ~vars e in
        let ct = close_top ~vars pt in
        let ct = apply_recursive pt.prec ct in
        let cmds, vars = transl_structure ~vars rem in
        (CTeval ct :: cmds, vars)
    | Tstr_value (rec_flag, [vb]) ->
        let ((id, desc), pt) = transl_binding ~vars ~rec_flag vb in
        let name, vars' =
          match id with
          | Some id ->
              let prec = if pt.pary > 0 then pt.prec else Nonrecursive in
              let desc = {desc with ce_rec = or_rec desc.ce_rec prec} in
              desc.ce_name, add_term ~toplevel:true (Path.Pident id) desc vars
          | None -> assert false
        in
        let cmds, vars' = transl_structure ~vars:vars' rem in
        if desc.ce_rec = Recursive then
          if pt.pary = 0 then
            not_allowed ~loc:it.str_loc "This recursive definition"
          else
            CTfixpoint (name, pt.pterm) :: cmds, vars'
        else
          let ct = close_top ~vars pt in
          let ct =
            if ct = pt.pterm && pt.prec = Recursive
            then abstract_recursive ct
            else apply_recursive pt.prec ct in
          CTdefinition (name, ct) :: cmds, vars'
    | _ ->
        not_allowed ~loc:it.str_loc "This structure item"

let make_ml_type vars =
  let cases =
    List.map
      (fun (_, ctd) ->
        ctd.ct_name, List.map (fun _ -> "_", ml_tid) ctd.ct_args, ml_tid)
      (Path.Map.bindings vars.type_map)
  in
  CTinductive { name = ml_type; args = []; kind = CTsort Set; cases }

let rec iota m n = if n <= 0 then [] else m :: iota (m+1) (n-1)
let iota_names m n t =
  List.map (fun i -> t ^ string_of_int i) (iota m n)

let make_coq_type vars =
  let make_case (_, ctd) =
    let constr = CTid ctd.ct_name in
    let n = List.length ctd.ct_args in
    let names = iota_names 1 n "T" in
    let lhs = ctapp constr (List.map ctid names)
    and rhs =
      match ctd.ct_def with
      | CT_def ct ->
          let subs =
            List.fold_left2
              (fun vars v1 v2 ->
                Vars.add v1 (CTapp (coq_tid, [CTid v2])) vars)
              Vars.empty ctd.ct_args names
          in
          coq_term_subst subs ct
      | _ ->
          if ctd.ct_name = "ml_ref" then (CTapp (CTid "loc", [CTid "T1"]))
          else CTid "unit"
    in lhs, rhs
  in
  let cases = List.map make_case (Path.Map.bindings vars.type_map) in
  CTfixpoint ("coq_type",
              CTabs ("T", Some ml_tid,
                     CTann (CTmatch (CTid "T", None, cases), CTsort Type)))

let make_compare_rec vars =
  let make_case (_, ctd) =
    let constr = CTid ctd.ct_name in
    let n = List.length ctd.ct_args in
    let names = iota_names 1 n "T" in
    let lhs = ctapp constr (List.map ctid names)
    and rhs =
      let ret =
        match ctd.ct_compare with
          None -> CTid "Fail"
        | Some ct -> ct
      in
      CTabs ("x", None, CTabs ("y", None, ret))
    in
    (lhs, rhs)
  in
  CTfixpoint ("compare_rec", CTabs (
              "T", Some ml_tid, CTabs (
              "h", Some (CTid "nat"), CTmatch (
              CTid "h", None,
              [CTapp (CTid "S", [CTid "h"]),
               CTmatch (
               CTid "T", Some ("T", CTprod (
                               None, CTapp(coq_tid,[CTid "T"]), CTprod (
                               None, CTapp(coq_tid,[CTid "T"]),
                               CTapp (CTid"M", [CTid "comparison"])))),
               List.map make_case (Path.Map.bindings vars.type_map));
               CTid "_", CTabs ("_", None, CTabs ("_", None, CTid "Fail"))]
             ))))

let transl_implementation _modname st =
  let cmds, vars = transl_structure ~vars:init_vars st.str_items in
  CTverbatim "From mathcomp Require Import all_ssreflect.\n\
Require Import Int63 cocti_defs.\n" ::
  make_ml_type vars ::
  CTverbatim "\nModule MLtypes.\n\
Definition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.\n\
revert T2; induction T1; destruct T2;\n\
  try (right; intro; discriminate); try (now left);\n\
  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);\n\
  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);\n\
  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);\n\
  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);\n\
  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);\n\
    right; injection; intros; contradiction.\n\
Defined.\n\n\
Local Definition ml_type := ml_type.\n\
Record key := mkkey {key_id : int; key_type : ml_type}.\n\
Variant loc : ml_type -> Type := mkloc : forall k : key, loc (key_type k).\n\
\n\
Section with_monad.\n\
Variable M : Type -> Type.\n\
Local" ::
  make_coq_type vars ::
  CTverbatim "End with_monad.\n\
End MLtypes.\n\
Export MLtypes.\n\
\n\
Module REFmonadML := REFmonad (MLtypes).\n\
Export REFmonadML.\n\
\n\
Definition coq_type := MLtypes.coq_type M.\n\
Definition empty_env := mkEnv 0%int63 nil.\
\n" ::
  make_compare_rec vars ::
  CTverbatim "Definition ml_compare := compare_rec.\
\n\
\nDefinition wrap_compare wrap T h x y : M bool :=\
\n  do c <- compare_rec T h x y; Ret (wrap c).\
\n\
\nDefinition ml_eq := wrap_compare (fun c => if c is Eq then true else false).\
\nDefinition ml_lt := wrap_compare (fun c => if c is Lt then true else false).\
\nDefinition ml_gt := wrap_compare (fun c => if c is Gt then true else false).\
\nDefinition ml_ne := wrap_compare (fun c => if c is Eq then false else true).\
\nDefinition ml_ge := wrap_compare (fun c => if c is Lt then false else true).\
\nDefinition ml_le := wrap_compare (fun c => if c is Gt then false else true).\
\n"
  :: cmds

open Format

let priority_level = function
  | CTid _ -> 10
  | CTcstr _ -> 10
  | CTprod (None, _, _) -> 2
  | CTapp (CTid "*", [_;_]) -> 3
  | CTapp (CTid "Bind", [_;CTabs _]) -> 0
  | CTapp (CTid "@cons", [_;_;_]) -> 0
  | CTapp (CTcstr "@cons", [_;_;_]) -> 0
  | CTapp _ -> 8
  | CTabs _ -> 0
  | CTsort _ -> 10
  | CTprod _ -> 0
  | CTmatch _ -> 10
  | CTann _ -> 10
  | CTlet _ -> 0
  | CTif _ -> 0

let string_of_sort = function
  | Type -> "Type"
  | Set -> "Set"
  | Prop -> "Prop"

let rec extract_args = function
  | CTabs (x, cto, ct) ->
      let (args, ct, ann) = extract_args ct in
      begin match args with
      | (argl, cto') :: args when cto = cto' ->
          (x :: argl, cto) :: args, ct, ann
      | _ -> ([x], cto) :: args, ct, ann
      end
  | CTann (ct, ann) -> ([], ct, Some ann)
  | ct -> ([], ct, None)

let rec print_term_rec lv ppf ty =
  if lv > priority_level ty then fprintf ppf "(%a)" (print_term_rec 0) ty else
  match ty with
  | CTid s | CTcstr s -> pp_print_string ppf s
  | CTprod (None, t1, t2) ->
      fprintf ppf "@[%a ->@ %a@]" (print_term_rec 3) t1 (print_term_rec 2) t2
  | CTapp (CTid "*", [t1; t2]) ->
      fprintf ppf "@[%a ->@ %a@]" (print_term_rec 3) t1 (print_term_rec 8) t2
  | CTapp (CTid "Bind", [ct1; CTabs (x, cto, ct2)]) ->
      fprintf ppf "@[do %s%a <-@ %a;@ %a@]"
        x print_type_ann cto
        (print_term_rec 1) ct1
        print_term ct2
  | CTapp (CTid "S", [t1]) ->
      fprintf ppf "@[%a.+1@]" (print_term_rec 10) t1
  | CTapp (CTid "@cons", [_;t1;t2])
  | CTapp (CTcstr "@cons", [_;t1;t2]) ->
      fprintf ppf "@[%a ::@ %a@]" (print_term_rec 8) t1 (print_term_rec 0) t2
  | CTapp (f, args) ->
      fprintf ppf "@[<2>%a@ %a@]" (print_term_rec 8) f
        (pp_print_list ~pp_sep:pp_print_space (print_term_rec 9)) args
  | CTabs _ ->
      fprintf ppf "@[<hov2>@[<hov2>fun";
      let t1 = print_args false ppf ty in
      fprintf ppf "@ =>@]@ %a@]" print_term t1
  | CTsort k -> pp_print_string ppf (string_of_sort k)
(*  | CTtuple tl ->
      fprintf ppf "(@[%a)@]"
        (pp_print_list (print_term_rec 1)
           ~pp_sep:(fun ppf () -> fprintf ppf ",@ "))
        tl *)
  | CTprod (Some x, t, t1) ->
      fprintf ppf "@[<hov2>@[<hov2>forall@ %s@ :@ %a@]@ %a@]"
        x print_term t print_term t1
  | CTmatch (ct, None, [(p1,ct1); (CTid"_",ct2)]) ->
      fprintf ppf
        "@[<hv>@[<2>@[<2>if@ %a@ is@ %a@]@;<1 -2>then@ %a@]@ @[<2>else@ %a@]@]"
        print_term ct
        print_term p1
        print_term ct1
        print_term ct2
  | CTmatch (ct, oret, cases) ->
      fprintf ppf "@[<hv>@[<2>match@ %a" print_term ct;
      Option.iter
        (fun (v, ct) ->
          fprintf ppf "@ as@ %s@ return@ %a" v print_term ct)
        oret;
      fprintf ppf "@ with@]";
      List.iter
        (fun (pat, ct) ->
          fprintf ppf "@ @[@[| %a =>@]@;<1 2>%a@]"
            print_term pat
            print_term ct)
        cases;
      fprintf ppf "@ end@]"
  | CTann (ct, cty) ->
      fprintf ppf "@[<1>(%a :@ %a)@]"
        print_term ct
        print_term cty
  | CTlet (x, None, ct1, ct2) ->
      fprintf ppf "@[<2>@[let %s" x;
      let ct1 = print_args true ppf ct1 in
      fprintf ppf "@ :=@]@ %a@;<1 -2>in@ %a@]"
        print_term ct1
        print_term ct2
  | CTlet (x, cto, ct1, ct2) ->
      fprintf ppf "@[<2>@[let %s%a :=@]@ %a@;<1 -2>in@ %a@]"
        x print_type_ann cto
        print_term ct1
        print_term ct2
  | CTif (ct1, ct2, ct3) ->
      fprintf ppf "@[if@;<1 2>%a@ then@;<1 2>%a@ else@;<1 2>%a@]"
        print_term ct1
        print_term ct2
        print_term ct3

and print_type_ann ppf = function
  | None -> ()
  | Some t -> fprintf ppf "@ : %a" (print_term_rec 0) t

and print_term ppf = print_term_rec 0 ppf

and print_args is_def ppf ct =
  let (args, ct, ann) = extract_args ct in
  let one_group = not is_def && List.length args = 1 in
  List.iter
    (fun (argl,cto) ->
      match cto with
      | None -> List.iter (fprintf ppf "@ %s") argl
      | _ when not is_def && List.for_all ((=) "_") argl ->
          List.iter (fprintf ppf "@ %s") argl
      | Some ct ->
          let po, pc = if one_group then "", "" else "(", ")" in
          fprintf ppf "@ @[<1>%s" po;
          List.iter (fprintf ppf "%s@ ") argl;
          fprintf ppf ":@ %a%s@]" print_term ct pc)
    args;
  (*if List.exists (fun (l,_) -> List.mem "h" l) args then
    fprintf ppf "@ {struct h}";*)
  if is_def then print_type_ann ppf ann;
  ct
  (* else may_app (fun cty ct -> CTann (ct, cty)) ann ct *)

let emit_def ppf def s ct =
  fprintf ppf "@[<2>@[<2>%s %s" def s;
  let ct = print_args true ppf ct in
  fprintf ppf " :=@]@ %a.@]@ " print_term ct

let print_arg_typed ppf (s, ct) =
  fprintf ppf "@ @[<1>(%s :@ %a)@]" s print_term ct

let emit_vernacular ppf = function
  | CTverbatim s            -> fprintf ppf "%s" s
  | CTdefinition (s, ct) -> emit_def ppf "Definition" s ct
  | CTfixpoint (s, ct)   -> emit_def ppf "Fixpoint" s ct
  | CTeval ct ->
      fprintf ppf "@[<2>Eval vm_compute in@ %a.@]@ " print_term ct
  | CTinductive td ->
      fprintf ppf "@[<hv2>@[<2>Inductive %s" td.name;
      List.iter (print_arg_typed ppf) td.args;
      fprintf ppf "@ :=@]";
      List.iter
        (fun (s, args, ret) ->
          fprintf ppf "@ @[<2>| %s" s;
          List.iter (print_arg_typed ppf) args;
          if td.args = [] && ret = CTid td.name then fprintf ppf "@]"
          else fprintf ppf "@ : %a@]" print_term ret)
        td.cases;
      fprintf ppf ".@]@ "

let emit_gallina _modname ppf cmds =
  pp_print_list ~pp_sep:pp_print_newline emit_vernacular ppf cmds

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
