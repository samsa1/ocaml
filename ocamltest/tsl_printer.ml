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

  and print_statement indent stmt =
    match stmt with
    | Not test ->
      pr "%snot" indent;
      print_statement "" test
    | Action { name; modifiers } ->
      pr "%s%s" indent name.node;
      begin match modifiers with
      | m :: tl ->
        pr " with %s" m.node;
        List.iter (fun m -> pr ", %s" m.node) tl;
      | [] -> ()
      end;
    | Environment_statement env ->
      print_env indent env

  and print_statements indent stmts =
    match stmts with
    | stmt :: tl ->
      print_statement indent stmt;
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

  and print_env indent e =
    match e.node with
    | Assignment (set, variable, value) ->
      pr "%s" indent;
      if set then pr "set ";
      pr "%s = \"%s\"" variable.node value.node;
    | Append (variable, value) ->
      pr "%s%s += \"%s\"" indent variable.node value.node;
    | Include ls ->
      pr "%sinclude %s" indent ls.node;
    | Unset ls ->
      pr "%sunset %s" indent ls.node;
  in
  print_ast " " ast;
