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
