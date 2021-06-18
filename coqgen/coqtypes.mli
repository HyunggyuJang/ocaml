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
open Coqdef

val transl_type :
  loc:Location.t ->
  env:Env.t ->
  vars:coq_env -> ?def:bool -> type_expr -> coq_term
val transl_coq_type :
  loc:Location.t ->
  env:Env.t -> vars:coq_env -> type_expr -> coq_term

val find_instantiation :
  loc:Location.t ->
  env:Env.t ->
  vars:coq_env ->
  coq_term_desc -> type_expr -> coq_term list

val ml_type : string
val ml_tid : coq_term
val mkcoqty : coq_term -> coq_term
val close_type : type_expr -> unit

val transl_typedecl :
    loc:Location.t ->
    env:Env.t ->
    vars:coq_env ->
    Ident.t -> type_declaration -> vernacular * coq_env

val enter_free_variables :
  loc:Location.t ->
  vars:coq_env ->
  type_expr ->
  type_expr list * Names.elt list * coq_env
