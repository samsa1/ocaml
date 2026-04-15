(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*            Samuel Vivien, projet Cambium, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2026 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)


type t

type path_eq_kind =
  | Module
  | Type

val empty : t

val is_empty : t -> bool
val has_error : Env.t -> t -> bool

val type_expr_printer : Types.type_expr Format_doc.printer ref
val print : t Format_doc.printer

val add_path_type_eq :
  Env.t -> Path.t -> Types.type_expr list -> Types.type_expr -> t -> t
val add_path_eq : Env.t -> path_eq_kind -> Path.t -> Path.t -> t -> t
val merge : Env.t -> t -> t -> t

val generalize : Types.functor_parameter -> t -> t

(* val iter : ('a -> t) -> t -> 'a list -> t
val iter2 : ('a -> 'b -> t) -> t -> 'a list -> 'b list -> t *)

val incompatible : (Env.t -> Types.type_expr -> Types.type_expr -> bool) ref
