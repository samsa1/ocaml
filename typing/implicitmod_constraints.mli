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

val empty : t

val is_empty : t -> bool
val size : t -> int
val has_error : Env.t -> t -> bool

val type_expr_printer : Types.type_expr Format_doc.printer ref
val print : t Format_doc.printer

val add : Path.t -> Types.type_expr list -> Types.type_expr -> t -> t
val merge : t -> t -> t

val generalize : Types.functor_parameter -> t -> t

val iter : ('a -> t) -> t -> 'a list -> t
val iter2 : ('a -> 'b -> t) -> t -> 'a list -> 'b list -> t

val incompatible : (Env.t -> Types.type_expr -> Types.type_expr -> bool) ref
