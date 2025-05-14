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

type ambiguity_explanation =
  | TwoSolutions of
      Types.module_type * Parsetree.module_expr * Parsetree.module_expr
  | RecLoop of Types.module_type * string
  | GenerativeApp of Types.module_type * string

type implicit_inference_fail_desc =
  | Ambiguity of ambiguity_explanation
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

let rec extract_arguments env args mty =
  match Env.scrape_alias env mty with
  | Mty_signature _ -> (args, mty)
  | Mty_functor (Unit, mty) ->
    extract_arguments env (Unit :: args) mty
  | Mty_functor (Named (_, n, arg_ty) as param, mty) ->
    let env = match n with
      | None -> env
      | Some id -> Env.add_module ~noalias:true id Mp_present IILocal arg_ty env
    in extract_arguments env (param :: args) mty
  | Mty_ident _ ->
      failwith "NYI : Inference with abstract signatures"
  | Mty_alias _ -> assert false

let rec prepare_args env args =
  match args with
  | [] -> ([], env)
  | Unit :: rest ->
      let args, env = prepare_args env rest in
      (None :: args, env)
  | Named (_, id, arg_ty) :: rest ->
      let args, env = prepare_args env rest in
      let arg_ty = open_module_type env arg_ty in
      let env = match id with
        | None -> env
        | Some id ->
          Env.add_module ~noalias:true id Mp_present IILocal arg_ty env
      in
      (Some (env, arg_ty) :: args, env)

let extract_function env depth mty =
  let rec aux d args mty =
    if d = 0
    then
      let (args, env) = prepare_args env args in
      Some (args, env, mty)
    else match args with
      | [] -> None
      | arg :: rest -> aux (d - 1) rest (Mty_functor (arg, mty))
  in
  let (args, mty) = extract_arguments env [] mty in
  aux depth args mty

let rec get_sig env depth mty =
    match Env.scrape_alias env mty with
    | Mty_signature sg -> (depth, sg)
    | Mty_functor (_, mty) -> get_sig env (depth + 1) mty
    | _ -> Misc.fatal_error "infer_implicit"

type solved_implicit_argument =
  | SIASolved of Parsetree.module_expr
  | SIAFailed of implicit_inference_fail

let rec find_module_expr ~loc trace env mty =
  let depth, sg = get_sig env 0 mty in
  let test_one_sig name path prev_sol =
    let mdecl = Env.find_strengthened_module ~aliasable:false path env in
    match extract_function env depth mdecl with
      | None -> prev_sol
      | Some (arguments, env_result, result) ->
        let snap = Btype.snapshot () in
        try begin
          ignore (Includemod.modtypes ~loc ~mark:false env_result result mty);
          if Misc.Stdlib.String.Set.mem name trace then begin
            Btype.backtrack snap;
            raise (ImplicitError ((loc, mty, Ambiguity (RecLoop (mty, name)))))
          end;
          let trace = Misc.Stdlib.String.Set.add name trace in
          let arguments = List.map (function
            | None -> SIAFailed ((loc, mty, Ambiguity (GenerativeApp (mty, name))))
            | Some (env, arg_mty) ->
              match find_module_expr ~loc trace env arg_mty with
              | marg -> SIASolved marg
              | exception ImplicitError ((_, _, Ambiguity _) as err) -> SIAFailed err
            ) arguments
          in
          let mexp = {
            pmod_desc = Pmod_ident { txt = Lident name; loc };
            pmod_loc = loc; pmod_attributes = [];
          } in
          let mexp = List.fold_right (fun marg mexp ->
              match marg with
              | SIASolved marg ->
                { pmod_desc = Pmod_apply (mexp, marg);
                  pmod_loc = loc; pmod_attributes = [] }
              | SIAFailed err -> Btype.backtrack snap; raise (ImplicitError err)
            ) arguments mexp
          in
          Btype.backtrack snap;
          match prev_sol with
          | None -> Some mexp
          | Some mexp' ->
            let explanation = TwoSolutions (mty, mexp, mexp') in
            raise (ImplicitError ((loc, mty, Ambiguity explanation)))
        end with
          | Includemod.Error _ | Ctype.Unify _
          | ImplicitError ((_, _, NoSolution)) ->
            Btype.backtrack snap; prev_sol
  in
  let ids = Env.find_structures sg env in
  match Misc.Stdlib.String.Map.fold test_one_sig ids None with
  | None -> raise (ImplicitError ((loc, mty, NoSolution)))
  | Some mexp -> mexp

let infer ~loc env mty =
  let mty = open_module_type env mty in
  try
    find_module_expr ~loc Misc.Stdlib.String.Set.empty env mty
  with ImplicitError (loc, _, err) ->
    raise (ImplicitError (loc, mty, err))

(* Error report *)
open Printtyp.Doc

let ambiguity_explanation ppf = function
  | TwoSolutions (mty, sol1, sol2) ->
      Format_doc.fprintf ppf
        "because two distinct solutions@ %a@ and@ %a@ \
         to the constraint@ %a@ where found"
          Pprintast.Doc.module_expr sol1
          Pprintast.Doc.module_expr sol2
          modtype mty
  | RecLoop (_mty, name) ->
      Format_doc.fprintf ppf
        "because the functor %s was called multiple time without@ \
         ensuring a decrease" name
  | GenerativeApp (mty, name) ->
      Format_doc.fprintf ppf
        "because a solution was found for@ %a@ by applying () to %s"
          modtype mty name

let report_implicit_error ~loc mty err =
  match err with
  | Ambiguity expl ->
      Location.errorf ~loc
          "@[<v>@[<2>Inference of signature %a@]@ \
           failed %a.@]"
           modtype mty ambiguity_explanation expl
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
