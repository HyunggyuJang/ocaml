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

open Asttypes
open Types
open Btype
open Coqdef

let ml_type = "ml_type"
let ml_tid = CTid ml_type
let coq_tid = CTid "coq_type"
let mkcoqty ct = ctapp coq_tid [ct]

let make_tuple_type ~def ctl =
  let unit = if def then "unit" else "ml_unit" in
  let pair = if def then "pair" else "ml_pair" in
  List.fold_left
    (fun ct ct' ->
      if ct = CTid unit then ct' else CTapp (CTid pair, [ct; ct']))
    (CTid unit) ctl

let with_snapshot ~vars f g =
  let snap = Btype.snapshot () in
  let x = f () in
  let vars = refresh_tvars vars in
  let y = g ~vars x in
  Btype.backtrack snap;
  y

let rec transl_type ~loc ~env ~vars ~def visited ty =
  if TypeSet.mem ty visited then not_allowed ~loc "recursive types" else
  let visited = TypeSet.add ty visited in
  let transl_rec = transl_type ~loc ~env ~vars ~def visited in
  match get_desc ty with
  | Tvar _ | Tunivar _ ->
      let tvars = (*if def then vars.ctvar_map else*) vars.tvar_map in
      CTid (TypeMap.find ty tvars)
  | Tarrow (Nolabel, t1, t2, _) ->
      let ct1 = transl_rec t1 and ct2 = transl_rec t2 in
      if def then CTprod (None, ct1, ctapp (CTid"M") [ct2])
      else ctapp (CTid "ml_arrow") [ct1; ct2]
  | Tarrow _ ->
      not_allowed ~loc "labels"
  | Ttuple tl ->
      make_tuple_type ~def (List.map transl_rec tl)
  | Tconstr (p, tl, _) ->
      begin match Path.Map.find p vars.type_map with
        desc ->
          let name =
            if def then
              match desc.ct_type with
                CTid name | CTapp (CTid name, _) -> name
              | _ -> not_allowed ~loc desc.ct_name
            else desc.ct_name
          in
          let transl_rec =
            if name = "list" || name = "ml_arrow" then transl_rec else
            transl_type ~loc ~env ~vars ~def:false visited in
          ctapp (CTid name) (List.map transl_rec tl)
      | exception Not_found ->
          with_snapshot ~vars
            (fun () -> Ctype.expand_head env ty)
            (fun ~vars ty' ->
              if eq_type ty ty' then not_allowed ~loc "This type";
              transl_type ~loc ~env ~vars ~def visited ty')
      end
  | Tnil ->
      CTid (if def then "unit" else "ml_unit")
  | Tobject _ | Tfield _ ->
      not_allowed ~loc "object types"
  | Tvariant _ ->
      not_allowed ~loc "polymorphic variants"
  | Tpoly (t1, vl) ->
      let vars =
        List.fold_left
          begin fun vars tv ->
            match get_desc tv with
            | Tunivar name -> add_tvar tv (fresh_var_name ~vars name) vars
            | _ -> assert false
          end
          vars vl
      in
      let ct1 = transl_type ~loc ~env ~vars ~def visited t1 in
      List.fold_right
        (fun tv ct -> CTprod (Some (TypeMap.find tv vars.tvar_map), ml_tid, ct))
        vl ct1
  | Tpackage _ ->
      not_allowed ~loc "first class modules"
  | Tlink _ | Tsubst _ ->
      assert false

let transl_type ~loc ~env ~vars ?(def=false) =
  transl_type ~loc ~env ~vars ~def TypeSet.empty
let transl_coq_type ~loc ~env ~vars ty =
  mkcoqty (transl_type ~loc ~env ~vars ty)

let find_instantiation ~loc ~env ~vars edesc ty =
  if edesc.ce_vars = [] then [] else
  let open Ctype in
  let ty0, ivars =
    let ty1 = newgenty (Ttuple (edesc.ce_type :: edesc.ce_vars)) in
    match get_desc (generic_instance ty1) with
      Ttuple (ty0 :: vars) -> ty0, vars
    | _ -> assert false
  in
  with_snapshot ~vars
    (fun () ->
      try unify env ty ty0
      with Unify _ -> not_allowed ~loc ("Type for " ^ edesc.ce_name))
    (fun ~vars () -> List.map (transl_type ~loc ~env ~vars) ivars)

let close_type ty =
  let vars = Ctype.free_variables ty in
  List.iter
    (fun ty ->
      let level = get_level ty in
      if level <> Btype.generic_level then
        Types.link_type ty (newty2 ~level Tnil))
    vars

let enter_tvars ~loc ~vars tvl =
  let names, vars =
    List.fold_left
      (fun (names, vars) tv -> match get_desc tv with
      | Tvar name ->
          let v = fresh_var_name ~vars name in
          v :: names, add_tvar tv v vars
      | _ -> not_allowed ~loc "Non-variable parameter")
      ([],vars) tvl
  in
  (List.rev names, vars)

let transl_typedecl ~loc ~env ~vars id td =
  let ml_name = fresh_name ~vars ("ml_" ^ Ident.name id) in
  let name = fresh_name ~vars (Ident.name id) in
  let vars = add_reserved name vars in
  let old_tvars = get_tvars vars in
  let params, vars = enter_tvars ~loc ~vars td.type_params in
  let ret_type = ctapp (CTid name) (List.map ctid params) in
  let ctd =
    { ct_name = ml_name; ct_args = params;
      ct_type = ret_type; ct_def = None;
      ct_compare = None; ct_constrs = [] } in
  let vars = add_type (Path.Pident id) ctd vars in
  if td.type_private <> Public then not_allowed ~loc "Private type";
  begin match td.type_kind with
  | Type_variant (cl, _) ->
      let names_types, vars =
        List.fold_left
          (fun (ntl, vars) (cd : Types.constructor_declaration) ->
            let cname = fresh_name ~vars (Ident.name cd.cd_id) in
            let vars = add_reserved cname vars in
            let args =
              match cd.cd_args with
              | Cstr_tuple tyl -> tyl
              | Cstr_record _ ->
                  not_allowed ~loc "Inline record"
            in
            if cd.cd_res <> None then not_allowed ~loc "GADT";
            let ctl_def =
              List.map (transl_type ~loc ~env ~vars ~def:true) args in
            let ctl =
              List.map (transl_type ~loc ~env ~vars) args in
            (cname, List.map (fun ct -> "_",ct) ctl_def, ctl) :: ntl,
            vars)
          ([],vars) cl
      in
      let names_types = List.rev names_types in
      let ctd =
        let cmp_cases =
          List.map (fun (cname, _, ctl) -> cname, ctl) names_types
        and ct_constrs =
          List.map2
            (fun cd (cname, _, _) -> (Ident.name cd.Types.cd_id, cname))
            cl names_types
        in
        { ctd with ct_constrs; ct_def = Some cmp_cases }
      in
      let vars = add_type (Path.Pident id) ctd vars in
      CTinductive
        { name; args = List.map (fun v -> v, CTsort Type) params;
          kind = CTsort Type;
          cases = List.map
            (fun (cname, args, _) -> cname, args, ret_type)
            names_types },
      set_tvars vars old_tvars
  | _ -> not_allowed ~loc "Non-inductive type definition"
  end

let enter_free_variables ~loc ~vars ty =
  (*close_type ty;*)
  let fvars = Ctype.free_variables ty in
  let fvars =
    List.filter (fun ty -> not (TypeMap.mem ty vars.tvar_map)) fvars in
  let (fvar_names, vars) =  enter_tvars ~loc ~vars fvars in
  (*List.iter (Format.eprintf "fvar=%a@." Printtyp.raw_type_expr) fvars;*)
  fvars, fvar_names, vars
