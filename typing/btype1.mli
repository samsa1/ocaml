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

(* Basic operations on core types *)

open Asttypes
open Types

(**** Sets, maps and hashtables of types ****)

module TypeSet : sig
    include Set.S with type elt = transient_expr
    val add: type_expr -> t -> t
    val mem: type_expr -> t -> bool
    val singleton: type_expr -> t
    val exists: (type_expr -> bool) -> t -> bool
    val elements: t -> type_expr list
  end
  
(**** Levels ****)

val generic_level: int
        (* level of polymorphic variables; = Ident.highest_scope *)
val lowest_level: int
        (* lowest level for type nodes; = Ident.lowest_scope *)

val static_row: row_desc -> bool
        (* Return whether the row is static or not *)


(**** Types ****)

val is_Tvar: type_expr -> bool
val is_Tunivar: type_expr -> bool
val is_Tconstr: type_expr -> bool
val is_poly_Tpoly: type_expr -> bool
val dummy_method: label
val type_kind_is_abstract: type_declaration -> bool
val type_origin: type_declaration -> type_origin
val label_is_poly: label_description -> bool

(**** polymorphic variants ****)

val is_fixed: row_desc -> bool
(* Return whether the row is directly marked as fixed or not *)


(**** Utilities for private abbreviations with fixed rows ****)
val row_of_type: type_expr -> type_expr
val has_constr_row: type_expr -> bool
val is_row_name: string -> bool
val is_constr_row: allow_ident:bool -> type_expr -> bool


(* Set the polymorphic variant row_name field *)
val set_static_row_name: type_declaration -> Path.t -> unit


(**** Type information getter ****)

val cstr_type_path : constructor_description -> Path.t

(**** Utilities for type traversal ****)

val iter_type_expr: ?allow_tsubst:bool -> (type_expr -> unit) ->
    type_expr -> unit
(* Iteration on types *)
val fold_type_expr: ?allow_tsubst:bool -> ('a -> type_expr -> 'a) ->
    'a -> type_expr -> 'a
val iter_row: (type_expr -> unit) -> row_desc -> unit
        (* Iteration on types in a row *)
val fold_row: ('a -> type_expr -> 'a) -> 'a -> row_desc -> 'a

(**** Utilities for copying ****)

val copy_type_desc:
    ?keep_names:bool -> (type_expr -> type_expr) -> type_desc -> type_desc
        (* Copy on types *)
val copy_row:
    (type_expr -> type_expr) ->
    bool -> row_desc -> bool -> type_expr -> row_desc

module For_copy : sig

  type copy_scope
        (* The private state that the primitives below are mutating, it should
           remain scoped within a single [with_scope] call.

           While it is possible to circumvent that discipline in various
           ways, you should NOT do that. *)

  val redirect_desc: copy_scope -> type_expr -> type_desc -> unit
        (* Temporarily change a type description *)

  val with_scope: (copy_scope -> 'a) -> 'a
        (* [with_scope f] calls [f] and restores saved type descriptions
           before returning its result. *)
end


val newgenty: type_desc -> type_expr
        (* Create a generic type *)
val newgenvar: ?name:string -> unit -> type_expr
        (* Return a fresh generic variable *)
val newgenstub: scope:int -> type_expr
        (* Return a fresh generic node, to be instantiated
           by [Transient_expr.set_stub_desc] *)
