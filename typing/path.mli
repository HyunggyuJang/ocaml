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

(* Access paths *)

type t =
    Pident of Ident.t
  | Pdot of t * string
  | Papply of t * t
  | Pextra_ty of t * extra_ty
  (** [Pextra_ty (p, extra)] is type path derived from [p]
      with characteristic [extra]
   *)
and extra_ty =
  | Pcstr_ty of string
  (** [Pextra_ty (p, Pcstr_ty c)] is the type of the inline record for
      constructor [c] inside type [p]
   *)
  | Pext_ty
  (** [Pextra_ty (p, Pext_ty)] is the type of the inline record for
      the extension constructor [p]
   *)
  | Pcls_ty
  (** [Pextra_ty (p, Pcls_ty)] is the hash type associated with
      the class type [p]
   *)

val same: t -> t -> bool
val compare: t -> t -> int
val compare_extra: extra_ty -> extra_ty -> int
val find_free_opt: Ident.t list -> t -> Ident.t option
val exists_free: Ident.t list -> t -> bool
val scope: t -> int
val flatten : t -> [ `Contains_apply | `Ok of Ident.t * string list ]

val name: ?paren:(string -> bool) -> t -> string
    (* [paren] tells whether a path suffix needs parentheses *)
val head: t -> Ident.t

val print: Format.formatter -> t -> unit

val heads: t -> Ident.t list

val last: t -> string

val is_constructor_typath: t -> bool

module Map : Map.S with type key = t
module Set : Set.S with type elt = t
