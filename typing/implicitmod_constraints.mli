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
  | Type of int

val empty : t

val has_error : Env.t -> t -> bool

val type_expr_printer : Types.type_expr Format_doc.printer ref
val print : t Format_doc.printer

val add_path_eq : Env.t -> path_eq_kind -> Path.t -> Path.t -> t -> t
val add_type_eq : Env.t -> Types.type_expr -> Types.type_expr -> t -> t
val merge : Env.t -> t -> t -> t

val get_def : Env.t -> t -> int -> Path.t -> Types.(type_expr list * type_expr) option

(* val generalize : Env.t -> Types.functor_parameter -> t -> t *)

(* val iter : ('a -> t) -> t -> 'a list -> t
val iter2 : ('a -> 'b -> t) -> t -> 'a list -> 'b list -> t *)

val expand_head_rigid : (Env.t -> Types.type_expr -> Types.type_expr) ref

type tmp
val of_tmp : Env.t -> tmp -> t
val is_empty : tmp -> bool
val empty_tmp : tmp
val merge_tmp : tmp -> tmp -> tmp
val generalize : Env.t -> Types.functor_parameter -> tmp -> tmp
val add_path_type_eq :
  Env.t -> Path.t -> Types.type_expr list -> Types.type_expr -> tmp -> tmp
