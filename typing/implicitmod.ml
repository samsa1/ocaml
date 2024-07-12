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

open Longident
open Asttypes
open Parsetree
open Types

type implicit_inference_fail_desc =
  | Ambiguity
  | NoSolution

type implicit_inference_fail =
  Location.t * Types.module_type * implicit_inference_fail_desc

exception ImplicitError of implicit_inference_fail

let rec open_signature_item env = function
  | Sig_type (id, ({type_manifest = None} as tdecl), r, v) ->
      if tdecl.type_arity <> 0
      then Misc.fatal_error "Abstract parametrized type not supported"
      else
          let tdecl = { tdecl with type_manifest = Some (Ctype.newvar ())} in
          Sig_type (id, tdecl, r, v)
  | Sig_module (id, mp, md, r, v) ->
      let md = { md with md_type = open_module_type env md.md_type} in
      Sig_module (id, mp, md, r, v)
  | Sig_modtype (_, { mtd_type = None}, _) ->
      Misc.fatal_error "Abstract sig not supported"
  | item -> item
and open_signature env s =
  List.map (open_signature_item env) s
and open_module_type env mty =
  match Env.scrape_alias env mty with
  | Mty_signature s -> Mty_signature (open_signature env s)
  | Mty_functor _ as mty -> mty
  | _ -> Misc.fatal_error "open_module_type"

let extract_function env mty =
  match Env.scrape_alias env mty with
  | Mty_signature _ -> ([], mty)
  | Mty_functor _ -> failwith "NYI : Inference through functors"
  | Mty_ident _ ->
      failwith "NYI : Inference with abstract signatures"
  | Mty_alias _ -> assert false

let rec find_module_expr ~loc env mty =
  let test_one_sig name path prev_sol =
    let mdecl = Env.find_strengthened_module ~aliasable:false path env in
    let arguments, result = extract_function env mdecl in
    let snap = Types.snapshot () in
    try begin
      ignore (Includemod.modtypes ~loc ~mark:false env result mty);
      let mexp = {
        pmod_desc = Pmod_ident { txt = Lident name; loc };
        pmod_loc = loc; pmod_attributes = [];
      } in
      let mexp = List.fold_right (fun arg_mty mexp ->
        let marg = find_module_expr ~loc env arg_mty in
        { pmod_desc = Pmod_apply (mexp, marg);
          pmod_loc = loc; pmod_attributes = [] }
      ) arguments mexp in
      Btype.backtrack snap;
      match prev_sol with
      | None -> Some mexp
      | Some _mexp' -> raise (ImplicitError ((loc, mty, Ambiguity)))
    end with
      | Includemod.Error _ | ImplicitError ((_, _, NoSolution)) ->
        Btype.backtrack snap; prev_sol
  in
  let sg = match mty with
    | Mty_signature sg -> sg
    | _ -> Misc.fatal_error "infer_implicit"
  in
  let ids = Env.find_structures sg env in
  match Misc.Stdlib.String.Map.fold test_one_sig ids None with
  | None -> raise (ImplicitError ((loc, mty, NoSolution)))
  | Some mexp -> mexp

let infer ~loc env mty =
  let mty = open_module_type env mty in
  find_module_expr ~loc env mty

(* Error report *)
open Printtyp.Doc

let report_implicit_error ~loc mty err =
  match err with
  | Ambiguity ->
      Location.errorf ~loc
          "@[<v>@[<2>Inference of signature %a@]@ \
           failed as multiple solutions were found.@]"
           modtype mty
  | NoSolution ->
      Location.errorf ~loc
          "@[<v>@[<2>Inference of signature %a@]@ \
            failed as no solution was found.@]"
            modtype mty

let () =
  Location.register_error_of_exn
    (function
      | ImplicitError ((loc, mty, err)) ->
          Some (report_implicit_error ~loc mty err)
      | _ -> None)
