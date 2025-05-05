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

(* Basic operations to create core types *)

open Types

val with_new_pool: level:int -> (unit -> 'a) -> 'a * transient_expr list
        (* [with_new_pool ~level f] executes [f] and returns the nodes
           that were created at level [level] and above *)
val add_to_pool: level:int -> transient_expr -> unit
        (* Add a type node to the pool associated to the level (which should
           be the level of the type node).
           Do nothing if [level = generic_level] or [level = lowest_level]. *)

val add_impl_to_pool: Typedtree.implicit_module_solver -> unit
        (* Add an implicit module to the pool associated to the level (which
           should be the level of the required signature). *)

val newty3: level:int -> scope:int -> type_desc -> type_expr
        (* Create a type with a fresh id *)
val newty2: level:int -> type_desc -> type_expr
        (* Create a type with a fresh id and no scope *)
