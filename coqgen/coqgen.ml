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

open Types
open Typedtree
open Coqdef
open Coqinit
open Coqtypes
open Coqcore

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
                Vars.add v1 (mkcoqty (CTid v2)) vars)
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
                               None, mkcoqty (CTid "T"), CTprod (
                               None, mkcoqty (CTid "T"),
                               CTapp (CTid"M", [CTid "comparison"])))),
               List.map make_case (Path.Map.bindings vars.type_map));
               CTid "_", CTabs ("_", None, CTabs ("_", None, CTid "Fail"))]
             ))))

let transl_implementation _modname st =
  let cmds, vars = transl_structure ~vars:init_vars st.str_items in
  let typedefs, cmds = 
    List.partition (function CTinductive _ -> true | _ -> false) cmds in
  CTverbatim "From mathcomp Require Import all_ssreflect.\n\
Require Import Int63 cocti_defs.\n" ::
  typedefs @
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
