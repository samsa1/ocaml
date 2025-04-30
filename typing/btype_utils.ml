(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*  Xavier Leroy and Jerome Vouillon, projet Cristal, INRIA Rocquencourt  *)
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

open Local_store
open Btype

(**** leveled type pool ****)
(* This defines a stack of pools of type nodes indexed by the level
   we will try to generalize them in [Ctype.with_local_level_gen].
   [pool_of_level] returns the pool in which types at level [level]
   should be kept, which is the topmost pool whose level is lower or
   equal to [level].
   [Ctype.with_local_level_gen] shall call [with_new_pool] to create
   a new pool at a given level. On return it shall process all nodes
   that were added to the pool.
   Remark: the only function adding to a pool is [add_to_pool], and
   the only function returning the contents of a pool is [with_new_pool],
   so that the initial pool can be added to, but never read from. *)

type pool = {level: int; mutable pool: transient_expr list; next: pool}
(* To avoid an indirection we choose to add a dummy level at the end of
   the list. It will never be accessed, as [pool_of_level] is always called
   with [level >= 0]. *)
let rec dummy = {level = max_int; pool = []; next = dummy}
let pool_stack = s_table (fun () -> {level = 0; pool = []; next = dummy}) ()

(* Lookup in the stack is linear, but the depth is the number of nested
   generalization points (e.g. lhs of let-definitions), which in ML is known
   to be generally low. In most cases we are allocating in the topmost pool.
   In [Ctype.with_local_gen], we move non-generalizable type nodes from the
   topmost pool to one deeper in the stack, so that for each type node the
   accumulated depth of lookups over its life is bounded by the depth of
   the stack when it was allocated.
   In case this linear search turns out to be costly, we could switch to
   binary search, exploiting the fact that the levels of pools in the stack
   are expected to grow. *)
let rec pool_of_level level pool =
  if level >= pool.level then pool else pool_of_level level pool.next

(* Create a new pool at given level, and use it locally. *)
let with_new_pool ~level f =
  let pool = {level; pool = []; next = !pool_stack} in
  let r =
    Misc.protect_refs [ R(pool_stack, pool) ] f
  in
  (r, pool.pool)

let add_to_pool ~level ty =
  if level >= generic_level || level <= lowest_level then () else
  let pool = pool_of_level level !pool_stack in
  pool.pool <- ty :: pool.pool

(**** Some type creators ****)

let newty3 ~level ~scope desc =
  let ty = proto_newty3 ~level ~scope desc in
  add_to_pool ~level ty;
  Transient_expr.type_expr ty

let newty2 ~level desc =
  newty3 ~level ~scope:Ident.lowest_scope desc

let () = Subst.newty2 := newty2