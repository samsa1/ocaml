(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Sebastien Hinderer, projet Gallium, INRIA Paris            *)
(*                                                                        *)
(*   Copyright 2016 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Printf
open Tsl_ast

let print_tsl_ast ~compact oc ast =
  let pr fmt (*args*) = fprintf oc fmt (*args*) in

  let rec print_ast indent (Ast (stmts, subs)) =
    print_statements indent stmts;
    print_forest indent subs;

  and print_sub indent ast =
    pr "{\n";
    print_ast (indent ^ "  ") ast;
    pr "%s}" indent;

  and print_statement stmt =
    match stmt with
    | Not test ->
      pr "not";
      print_statement test
    | Action { name; modifiers } ->
      pr "%s" name.node;
      begin match modifiers with
      | m :: tl ->
        pr " with %s" m.node;
        List.iter (fun m -> pr ", %s" m.node) tl;
      | [] -> ()
      end;
    | Environment_statement env ->
      print_env env

  and print_statements indent stmts =
    match stmts with
    | stmt :: tl ->
      pr "%s" indent;
      print_statement stmt;
      pr ";\n";
      if tl <> [] && not compact then pr "\n";
      print_statements indent tl;
    | [] -> ()

  and print_forest indent subs =
    if subs <> [] then begin
      pr "%s" indent;
      List.iter (print_sub indent) subs;
      pr "\n";
    end

  and print_env e =
    match e.node with
    | Assignment (set, variable, value) ->
      if set then pr "set ";
      pr "%s = \"%s\"" variable.node value.node;
    | Append (variable, value) ->
      pr "%s += \"%s\"" variable.node value.node;
    | Include ls ->
      pr "include %s" ls.node;
    | Unset ls ->
      pr "unset %s" ls.node;
  in
  print_ast " " ast;
