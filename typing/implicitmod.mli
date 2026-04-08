(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*            Samuel Vivien, projet Cambium, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Inference of implicit module expression

  {b Warning:} this module is unstable and part of
  {{!Compiler_libs}compiler-libs}.

*)

val type_module :
    (Env.t -> Parsetree.module_expr -> Typedtree.module_expr * Shape.t) ref

val type_one_application_to_path :
    (loc:Location.t -> Env.t -> Typedtree.module_expr -> Path.t ->
      Typedtree.module_expr -> Typedtree.module_expr option) ref

val open_module_type : Env.t -> Types.module_type -> Types.module_type

val infer :
    loc:Location.t -> Env.t -> Types.module_type -> Parsetree.module_expr
