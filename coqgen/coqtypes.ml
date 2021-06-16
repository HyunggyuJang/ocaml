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
      CTid (TypeMap.find ty vars.tvar_map)
  | Tarrow (Nolabel, t1, t2, _) ->
      let arrow = if def then "->" else "ml_arrow" in
      CTapp (CTid arrow, [transl_rec t1; transl_rec t2])
  | Tarrow _ ->
      not_allowed ~loc "labels"
  | Ttuple tl ->
      make_tuple_type ~def (List.map transl_rec tl)
  | Tconstr (p, tl, _) ->
      begin match Path.Map.find p vars.type_map with
        desc ->
          let name =
            if def then
              match desc.ct_def with
                CT_def (CTapp (CTid name, _), _) -> name
              | _ -> not_allowed ~loc desc.ct_name
            else desc.ct_name
          in
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

let enter_free_variables ~loc ~vars ty =
  (*close_type ty;*)
  let fvars = Ctype.free_variables ty in
  let fvars =
    List.filter (fun ty -> not (TypeMap.mem ty vars.tvar_map)) fvars in
  let (fvar_names, vars) =  enter_tvars ~loc ~vars fvars in
  (*List.iter (Format.eprintf "fvar=%a@." Printtyp.raw_type_expr) fvars;*)
  fvars, fvar_names, vars
