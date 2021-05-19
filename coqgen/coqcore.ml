(**************************************************************************)
(*                                                                        *)
(*                             OCaml in Coq                               *)
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

type term_props =
    { pterm: coq_term; prec: rec_flag; pary: int }

let stdlib = Path.Pident (Ident.create_persistent "Stdlib")
let coqgen = Path.Pident (Ident.create_persistent "coqgen")
let stdlib_ref = Path.Pdot (stdlib, "ref")
let newgenconstr p tl = newgenty (Tconstr (p, tl, ref Mnil))
let newgenarrow t1 t2 = newgenty (Tarrow (Nolabel, t1, t2, Cok))

let xy = [CTid"x"; CTid"y"]

let init_type_map =
  List.fold_left
    (fun map (rt, lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) rt lid in
      Path.Map.add path desc map)
    Path.Map.empty
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

let init_term_map =
  let int_to_int = newgenarrow Predef.type_int Predef.type_int in
  let int_to_int_to_int = newgenarrow Predef.type_int int_to_int in
  List.fold_left
    (fun map (lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) stdlib lid in
      Path.Map.add path desc map)
    Path.Map.empty (
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

let type_map = ref (init_type_map : coq_type_desc Path.Map.t)
let term_map = ref (init_term_map : coq_term_desc Path.Map.t)

let get_used_top_names =
  let used_top_names = ref Names.empty in
  let last_type_map = ref !type_map in
  let last_term_map = ref !term_map in
  fun () ->
    let tm = !type_map and em = !term_map in
    if tm != !last_type_map || em != !last_term_map then begin
      let names =
        Path.Map.fold
          (fun _ td ->
            List.fold_right Names.add
              (td.ct_name :: List.map snd td.ct_constrs))
          tm Names.empty in
      let names =
        Path.Map.fold (fun _ td -> Names.add td.ce_name) em names in
      used_top_names := names;
      last_type_map := tm;
      last_term_map := em;
    end;
    !used_top_names

let fresh_name ?(name = "T") (used : string -> bool) =
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

let rec transl_type ~loc (vars : string TypeMap.t) visited ty =
  let ty = repr ty in
  if TypeSet.mem ty visited then not_allowed ~loc "recursive types" else
  let visited = TypeSet.add ty visited in
  let transl_rec = transl_type ~loc vars visited in
  match ty.desc with
  | Tvar _ | Tunivar _ ->
      CTid (TypeMap.find ty vars)
  | Tarrow (Nolabel, t1, t2, _) ->
      CTapp (CTid "ml_arrow", [transl_rec t1; transl_rec t2])
  | Tarrow _ ->
      not_allowed ~loc "labels"
  | Ttuple tl ->
      make_tuple_type (List.map transl_rec tl)
  | Tconstr (p, tl, _) ->
      let desc = Path.Map.find p !type_map in
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
            | Tunivar name -> TypeMap.add tv (fresh_var_name vars name) vars
            | _ -> assert false
          end
          vars vl
      in
      let ct1 = transl_type ~loc vars visited t1 in
      List.fold_right
        (fun tv ct -> CTprod (Some (TypeMap.find tv vars), ml_tid, ct))
        vl ct1
  | Tpackage _ ->
      not_allowed ~loc "first class modules"
  | Tlink _ | Tsubst _ ->
      assert false

let transl_type ~loc vars = transl_type ~loc vars TypeSet.empty

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

let used_term_name vars s =
  Names.mem s (get_used_top_names ()) ||
  Ident.fold_name (fun _ desc b -> b || desc.ce_name = s) vars false

let fresh_term_name ?name vars =
  fresh_name ?name (used_term_name vars)

let used_term_names names s =
  Names.mem s (get_used_top_names ()) || Names.mem s names

let fresh_term_names ~names name =
  fresh_name ~name (used_term_names names)

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

let enter_free_variables tvars ty =
  (*close_type ty;*)
  let fvars = Ctype.free_variables ty in
  let fvars = List.filter (fun ty -> not (TypeMap.mem ty tvars)) fvars in
  let (fvar_names, tvars) =
    List.fold_left
      (fun (names, tvars) tv -> match tv.desc with
      | Tvar name ->
          let v = fresh_var_name tvars name in
          v :: names, TypeMap.add tv v tvars
      | _ -> assert false)
      ([],tvars) fvars
  in
  (*List.iter (Format.eprintf "fvar=%a@." Printtyp.raw_type_expr) fvars;*)
  fvars, List.rev fvar_names, tvars

let refresh_tvars tvars =
  TypeMap.fold (fun ty -> TypeMap.add (repr ty)) tvars TypeMap.empty

let rec fun_arity e =
  match e.exp_desc with
  | Texp_function
    {cases=[{c_lhs={pat_desc=(Tpat_var _|Tpat_any)};c_guard=None;c_rhs}]} ->
      1 + fun_arity c_rhs
  | Texp_function _ -> 1
  | _ -> 0

let rec shrink_purary_val ~names ~args p1 p2 ct =
  if p1 <= 1 then ctapp ct (List.rev args) else
  let x = fresh_term_names ~names "x" in
  let ct1 =
    CTabs (x, None,
           shrink_purary_val
             ~names:(Names.add x names) ~args:(CTid x :: args)
             (p1-1) (p2-1) ct)
  in
  if p2 <= 0 then ctRet ct1 else ct1

let rec shrink_purary_rec ~names p1 p2 ct =
  assert (p2 <= p1);
  if p1 <= 0 || p1 = p2 then ct else
  let ct2 =
    match ct with
    | CTabs (x, t, ct1) ->
        let names = Names.add x names in
        CTabs (x, t, shrink_purary_rec ~names (p1-1) (p2-1) ct1)
    | _ ->
        shrink_purary_val ~names ~args:[] p1 p2 ct
  in
  if p2 <= 0 then ctRet ct2 else ct2

let shrink_purary ~names pt p2 =
  if pt.pary = p2 then pt else
  {pterm = shrink_purary_rec ~names pt.pary p2 pt.pterm;
   prec = pt.prec; pary = p2}

let nullary ~names pt =
  shrink_purary ~names pt 0

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

let is_primitive s =
  String.length s >= 2 && s.[0] = '@'

let type_ident ~loc ~tvars env desc ty =
  let snap = Btype.snapshot () in
  let ivars = find_instantiation ~loc env desc ty in
  (*List.iter (Format.eprintf "ivar=%a@." Printtyp.raw_type_expr) ivars;*)
  let tvars = refresh_tvars tvars in
  let f = CTid desc.ce_name in
  let args = List.map (transl_type ~loc tvars) ivars in
  let args =
    if is_primitive desc.ce_name
    then List.map (fun x -> CTapp (coq_tid, [x])) args
    else args in
  Btype.backtrack snap;
  let args =
    if desc.ce_rec = Recursive then args @ [CTid"h"] else args in
  {pterm = ctapp f args; prec = desc.ce_rec; pary = desc.ce_purary}

let rec transl_exp ~(tvars : string TypeMap.t) ~(vars : coq_term_desc Ident.tbl)
    e =
  let loc = e.exp_loc in
  close_type e.exp_type;
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
      type_ident ~loc ~tvars e.exp_env desc e.exp_type
  | Texp_constant (Const_int n) ->
      {pterm = CTid (string_of_int n ^ "%int63"); prec = Nonrecursive;
       pary = 1 }
  | Texp_let (Nonrecursive, vbl, body) ->
      let ctl =
        List.map (transl_binding ~tvars ~vars ~rec_flag:Nonrecursive) vbl in
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
                Ident.add id desc vars
            | None -> vars)
          id_descs
          vars
      in
      let pbody = transl_exp ~tvars ~vars body in      
      let pat = name_tuple names in
      let ct = make_tuple (List.map (fun ct -> ct.pterm) ctl) in
      let names = Names.of_list (vars_names vars) in
      begin match pat, id_descs with
      | CTid v, [(_, desc)] ->
          if desc.ce_purary = 0 then
            let pbody = nullary ~names pbody in
            {pbody with pterm = ctBind ct (CTabs (v, None, pbody.pterm))}
          else
            {pbody with pterm = CTlet (v, None, ct, pbody.pterm)}
      | _ ->
          if List.exists (fun (_,desc) -> desc.ce_purary = 0) id_descs then
            let pbody = nullary ~names pbody in
            let pbody =
              List.fold_right
                (fun (_,{ce_name; ce_purary}) pbody ->
                  if ce_purary <> 0 then pbody else
                  {pbody with pterm =
                   ctBind (CTid ce_name) (CTabs (ce_name, None, pbody.pterm))})
                id_descs pbody in
            let v = fresh_term_name vars in
            {pbody with pterm =
             ctBind ct (CTabs (v, None,
                               CTmatch (CTid v, None, [pat, pbody.pterm])))}
          else
            {pbody with pterm = CTmatch (ct, None, [pat, pbody.pterm])}
      end
  | Texp_sequence (e1, e2) ->
      let names = Names.of_list (vars_names vars) in
      let ct1 = nullary ~names (transl_exp ~tvars ~vars e1) in
      let ct2 = nullary ~names (transl_exp ~tvars ~vars e2) in
      {pterm = ctBind ct1.pterm (CTabs ("_", None, ct2.pterm));
       prec = or_rec ct1.prec ct2.prec; pary = 0}
  | Texp_function
      {arg_label = Nolabel; param = _;
       cases = [{c_lhs = {pat_desc; pat_type; pat_loc};
                 c_rhs; c_guard = None}]} ->
      let (arg, vars) =
        match pat_desc with
          Tpat_any -> "_", vars
        | Tpat_var (id, _) ->
            let arg = fresh_term_name vars ~name:(Ident.name id) in
            let desc =
              {ce_name = arg; ce_type = pat_type;
               ce_vars = []; ce_purary = 1; ce_rec = Nonrecursive} in
            arg, Ident.add id desc vars
        | _ -> not_allowed ~loc:pat_loc "This pattern"
      in
      let cty = transl_type ~loc:pat_loc tvars pat_type in
      let cty = CTapp(coq_tid,[cty]) in
      let ct = transl_exp ~tvars ~vars c_rhs in
      let ct =
        match ct.pterm with
          CTabs _ | CTann _ -> ct
        | pt ->
            if ct.pary >= 2 then ct else
            let cty = transl_type ~loc:c_rhs.exp_loc tvars c_rhs.exp_type in
            let cty = CTapp (coq_tid,[cty]) in
            let cty = if ct.pary = 0 then CTapp (CTid"M", [cty]) else cty in
            {ct with pterm = CTann (pt, cty)}
      in
      {pterm = CTabs (arg, Some cty, ct.pterm);
       prec  = ct.prec; pary  = ct.pary + 1}
  | Texp_apply (f, args)
    when List.for_all (function (Nolabel,Some _) -> true | _ -> false) args ->
      let args =
        List.map (function (_,Some arg) -> arg | _ -> assert false) args in
      let ct = transl_exp ~tvars ~vars f in
      let ctl = List.map (transl_exp ~tvars ~vars) args in
      let prec =
        if List.exists (fun ct -> ct.prec = Recursive) (ct :: ctl)
        then Recursive else Nonrecursive
      in
      let names = Names.of_list (vars_names vars) in
      let args, binds, names =
        List.fold_right
          (fun ct (args, binds, names) ->
            if ct.pary >= 1 then
              ((shrink_purary ~names ct 1).pterm :: args, binds, names)
            else
              let v = fresh_term_names ~names "v" in
              (CTid v :: args, (v, ct.pterm) :: binds, Names.add v names))
          ctl ([],[],names)
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
        (nullary ~names ct) binds
  | Texp_construct (_, cd, []) ->
      let name, tl =
        let path, tl =
          match repr cd.cstr_res with
          | {desc = Tconstr (path, tl, _)} -> path, tl
          | _ -> assert false
        in
        try
          let ct = Path.Map.find path !type_map in
          List.assoc cd.cstr_name ct.ct_constrs, tl
        with Not_found -> 
          not_allowed ~loc
            ("The constructor " ^ cd.cstr_name ^ " of type " ^ Path.name path)
      in
      let ce =
        {ce_name = name;
         ce_type = List.fold_right newgenarrow cd.cstr_args cd.cstr_res;
         ce_vars = tl;
         ce_rec = Nonrecursive;
         ce_purary = cd.cstr_arity + 1}
      in
      type_ident ~loc ~tvars e.exp_env ce e.exp_type
  | Texp_construct (lid, cd, args) ->
      let ty =
        List.fold_right
          (fun arg t2 ->
            let t1 = arg.exp_type in
            newty2 (min t1.level t2.level)
              (Tarrow (Nolabel, arg.exp_type, t2, Cok)))
          args e.exp_type
      in
      let constr =
        {e with exp_desc = Texp_construct (lid, cd, []); exp_type = ty} in
      let args = List.map (fun e -> (Nolabel, Some e)) args in
      let app = {e with exp_desc = Texp_apply (constr, args)} in
      transl_exp ~tvars ~vars app
  | Texp_ifthenelse (be, e1, e2) ->
      let ct = transl_exp ~tvars ~vars be
      and ct1 = transl_exp ~tvars ~vars e1
      and ct2 =
        match e2 with
        | None    -> {pterm = CTid "tt"; prec = Nonrecursive; pary = 1}
        | Some e2 -> transl_exp ~tvars ~vars e2
      in
      let names = Names.of_list (vars_names vars) in
      let prec = or_rec ct.prec (or_rec ct1.prec ct2.prec) in
      if ct.pary = 0 then
        let v = fresh_term_names ~names "v" in
        let names = Names.add v names in
        let ct1 = nullary ~names ct1
        and ct2 = nullary ~names ct2 in
        {pterm =
         ctBind ct.pterm (CTabs (v, None, CTif (CTid v, ct1.pterm, ct2.pterm)));
         pary = 0; prec}
      else
        let pary = min ct1.pary ct2.pary in
        let ct1 = shrink_purary ~names ct1 pary
        and ct2 = shrink_purary ~names ct2 pary in
        {pterm = CTif (ct.pterm, ct1.pterm, ct2.pterm); prec; pary}
  | _ ->
      not_allowed ~loc "This kind of term"

and transl_binding ~(tvars : string TypeMap.t) ~(vars : coq_term_desc Ident.tbl)
    ~rec_flag vb =
  let name, id =
    match vb.vb_pat.pat_desc with
      Tpat_any -> "_", None
    | Tpat_var (id, _) -> Ident.name id, Some id
    | Tpat_construct (_, {cstr_name="()"}, [], _) -> "_", None
    | _ -> not_allowed ~loc:vb.vb_pat.pat_loc "This pattern"
  in
  let ty = vb.vb_expr.exp_type in
  (*Format.eprintf "exp_type=%a@." Printtyp.raw_type_expr ty;*)
  let fvars, fvar_names, tvars = enter_free_variables tvars ty in
  let desc =
    {ce_name = name; ce_type = ty; ce_vars = fvars;
     ce_rec = rec_flag; ce_purary = fun_arity vb.vb_expr}
  in
  let vars =
    match rec_flag, id with
    | Recursive, Some id -> Ident.add id desc vars
    | _ -> vars
  in
  let ct = transl_exp ~tvars ~vars vb.vb_expr in
  let prec = ct.prec in
  let ct, desc =
    match rec_flag with
    | Recursive ->
        let names = Names.of_list (vars_names vars) in
        let ct = shrink_purary ~names ct desc.ce_purary in
        CTabs ("h", Some (CTid"nat"), insert_guard ct.pterm), desc
      (*
        let ct =
          if purary = desc.ce_purary then ct else
          let names = Names.of_list (vars_names vars) in
          shrink_purary ~names purary 1 ct
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
        let pt =
          if ct.prec = Recursive then CTabs ("h", Some (CTid"nat"), ct.pterm)
          else ct.pterm in
        pt, {desc with ce_purary = ct.pary; ce_rec = ct.prec}
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

let rec transl_structure ~(vars : coq_term_desc Ident.tbl) = function
    [] -> []
  | it :: rem -> match it.str_desc with
    | Tstr_eval (e, _) ->
        let _fvars, fvar_names, tvars =
          enter_free_variables TypeMap.empty e.exp_type in
        let pt = transl_exp ~tvars ~vars e in
        let args =
          if pt.pary = 0 then [CTid "empty_env"] else [] in
        let ct = ctapp pt.pterm args in
        let ct =
           List.fold_right (fun tv ct -> CTabs (tv, Some ml_tid, ct))
             fvar_names ct
        in
        let ct = apply_recursive pt.prec ct in
        CTeval ct :: transl_structure ~vars rem
    | Tstr_value (rec_flag, [vb]) ->
        let ((id, desc), ct) =
          transl_binding ~tvars:TypeMap.empty ~vars ~rec_flag vb in
        let name, vars =
          match id with
          | Some id -> Ident.name id, Ident.add id desc vars
          | None -> assert false
        in
        let rem =  transl_structure ~vars rem in
        if desc.ce_rec = Recursive then
          CTfixpoint (name, ct.pterm) :: rem
        else
          let ct = apply_recursive ct.prec ct.pterm in
          CTdefinition (name, ct) :: rem
    | _ ->
        not_allowed ~loc:it.str_loc "This structure item"

let make_ml_type () =
  let cases =
    List.map
      (fun (_, ctd) ->
        ctd.ct_name, List.map (fun _ -> "_", ml_tid) ctd.ct_args, ml_tid)
      (Path.Map.bindings !type_map)
  in
  CTinductive { name = ml_type; args = []; kind = CTsort Set; cases }

let rec iota m n = if n <= 0 then [] else m :: iota (m+1) (n-1)
let iota_names m n t =
  List.map (fun i -> t ^ string_of_int i) (iota m n)

let make_coq_type () =
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
  let cases = List.map make_case (Path.Map.bindings !type_map) in
  CTfixpoint ("coq_type",
              CTabs ("T", Some ml_tid,
                     CTann (CTmatch (CTid "T", None, cases), CTsort Type)))

let make_compare_rec () =
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
               List.map make_case (Path.Map.bindings !type_map));
               CTid "_", CTabs ("_", None, CTabs ("_", None, CTid "Fail"))]
             ))))

let transl_implementation _modname st =
  let cmds = transl_structure ~vars:Ident.empty st.str_items in
  CTverbatim "From mathcomp Require Import all_ssreflect.\n\
Require Import Int63 cocti_defs.\n" ::
  make_ml_type () ::
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
  make_coq_type () ::
  CTverbatim "End with_monad.\n\
End MLtypes.\n\
Export MLtypes.\n\
\n\
Module REFmonadML := REFmonad (MLtypes).\n\
Export REFmonadML.\n\
\n\
Definition coq_type := MLtypes.coq_type M.\n\
Definition empty_env := mkEnv 0%int63 nil.\n\
\n\
Definition Fix T1 T2\
\n  (F : coq_type (ml_arrow (ml_arrow T1 T2) (ml_arrow T1 T2)))\
\n  : M (coq_type (ml_arrow T1 T2)) :=\
\n  do r <- newref (ml_arrow T1 T2) (fun x => Fail);\
\n  let f x :=  do f <- getref _ r; AppM (F f) x in\
\n  do _ <- setref _ r f; Ret f.\
\n" ::
  make_compare_rec () ::
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
  | CTapp _ -> 4
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
      fprintf ppf "@[%a ->@ %a@]" (print_term_rec 3) t1 (print_term_rec 4) t2
  | CTapp (CTid "Bind", [ct1; CTabs (x, cto, ct2)]) ->
      fprintf ppf "@[do %s%a <-@ %a;@ %a@]"
        x print_type_ann cto
        (print_term_rec 1) ct1
        print_term ct2
  | CTapp (CTid "S", [t1]) ->
      fprintf ppf "@[%a.+1@]" (print_term_rec 10) t1
  | CTapp (f, args) ->
      fprintf ppf "@[<2>%a@ %a@]" (print_term_rec 4) f
        (pp_print_list ~pp_sep:pp_print_space (print_term_rec 5)) args
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
