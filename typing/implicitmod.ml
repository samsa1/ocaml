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

module FuncOrder : sig
  type t
  val empty : t
  val update_map : Env.t -> t -> string -> Types.module_type -> t option
end = struct
  type el =
    | Depth of int
    | UnifDepth of int

  type t = el Misc.Stdlib.String.Map.t
  let empty = Misc.Stdlib.String.Map.empty

  let mini = Depth (-1)

  let max x y =
    match x, y with
    | UnifDepth xi, UnifDepth yi -> UnifDepth (Int.max xi yi)
    | UnifDepth i, _ | _, UnifDepth i -> UnifDepth i
    | Depth xi, Depth yi -> Depth (Int.max xi yi)

    let lt x y =
    match x, y with
    | UnifDepth xi, UnifDepth yi | Depth xi, Depth yi -> xi < yi
    | UnifDepth _, _ -> true
    | _, UnifDepth _ -> false

  let is_smaller map name v =
    match Misc.Stdlib.String.Map.find name map with
    | v' -> lt v v'
    | exception Not_found -> true

  let rec type_expr env depth ty =
    let ty' = Ctype.expand_head env ty in
    match get_desc ty' with
    | Tvar _ ->
      if get_level ty' < Btype.generic_level then UnifDepth depth
      else Depth depth
    | _ ->
      Btype.fold_type_expr
        (fun acc ty -> max acc (type_expr env (depth + 1) ty)) (Depth depth) ty'

  let type_declaration env td =
    match td.type_manifest with
    | None -> mini
    | Some ty ->
      if td.type_arity = 0 then type_expr env 0 ty
      else assert false (* TODO *)

  let rec signature_item env item =
    match item with
    | Sig_value (_, vd, _) -> type_expr env 0 vd.val_type
    | Sig_type (_, td, _, _) -> type_declaration env td
    | Sig_typext (_, _, _, _) -> mini
    | Sig_module (_, _, { md_type = mty }, _, _)
    | Sig_modtype (_, { mtd_type = Some mty }, _) -> module_type env mty
    | Sig_modtype (_, { mtd_type = None }, _) ->
      assert false (* TODO : Abstract module type *)
    | Sig_class (_, _cd, _, _) ->
      assert false (* TODO : class_declaration cd *)
    | Sig_class_type (_, _cd, _, _) ->
      assert false (* TODO : class_type_declaration cd *)
  and signature env maxi = function
    | [] -> maxi
    | item :: rest -> signature env (max maxi (signature_item env item)) rest
  and module_type env mty =
    match Env.scrape_alias env mty with
    | Mty_signature s -> signature env mini s
    | Mty_functor (Unit, mty2)
    | Mty_functor (Newtype _, mty2) -> module_type env mty2
    | Mty_functor (Named (_, id, mty1), mty2) ->
      let d_mty1 = module_type env mty1 in
      let env =
        match id with
        | None -> env
        | Some id -> Env.add_module ~noalias:true id Mp_present IILocal mty1 env
      in
      max d_mty1 (module_type env mty2)
    | Mty_ident _ -> assert false (* TODO : Abstract module type *)
    | Mty_alias _ -> assert false (* Should not happen *)

  let update_map env m name mty =
    let v = module_type env mty in
    if is_smaller m name v
    then Some (Misc.Stdlib.String.Map.add name v m)
    else None
end

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
  | Mty_functor _ as mty -> mty (* TODO *)
  | _ -> Misc.fatal_error "open_module_type"

let rec extract_arguments env args mty =
  match Env.scrape_alias env mty with
  | Mty_signature _ -> (args, mty)
  | Mty_functor (Unit, mty) ->
    extract_arguments env (Unit :: args) mty
  | Mty_functor (Newtype id as param, mty) ->
    let decl = Ctype.new_local_type ~loc:Location.none Definition in
    let env = Env.add_type ~check:true id decl env in
    extract_arguments env (param :: args) mty
  | Mty_functor (Named (_, n, arg_ty) as param, mty) ->
    let env = match n with
      | None -> env
      | Some id ->
        Env.add_module ~noalias:true id Mp_present IILocal arg_ty env
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
  | Newtype _id :: _rest -> assert false
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

type implicit_inference_solution = {
  psol : Parsetree.module_expr;
  tsol : Typedtree.module_expr;
}

type problem = {
  env : Env.t;
  signature : Types.module_type;
  nargs : int;
}

type implicit_inference = {
  problem : problem;
  desc : implicit_inference_desc;
}
and status =
  | RecLimit of (Env.t * Types.module_type) option list
  | Node of implicit_inference option list * int
and implicit_inference_desc =
  | Solved of implicit_inference_solution
  | Working of {
      solutions : implicit_inference_solution list;
      current : (string * Env.t * Types.module_type * status) option;
      next : (string * Path.t) Seq.t;
    }
  | NoSolution

exception ImplicitError of Location.t * implicit_inference

let print_it_with_holes fmt node =
  let nb = ref 1 in
  let rec print_node fmt {desc; _} =
    match desc with
    | Solved {psol; _} ->
      Pprintast.Doc.module_expr fmt psol
    | NoSolution ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_with_holes]"
    | Working { solutions = _ :: _ :: _; _ }
    | Working { current = Some (_, _, _, RecLimit _) } ->
      Format_doc.fprintf fmt "?%d" !nb;
      incr nb;
    | Working { current = Some (_, _, _, Node ([], _))} ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_with_holes]"
    | Working { current = Some (name, _, _, Node (args, _))} ->
      Format_doc.fprintf fmt "@[<hov2>%s@ %a@]"
        name
        print_args args
    | Working { solutions = _; current = None; next = _} ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_with_holes]"
  and print_args fmt = function
    | [] -> ()
    | [arg] -> print_arg fmt arg
    | hd :: tl ->
      Format_doc.fprintf fmt "%a@ %a" print_arg hd print_args tl
  and print_arg fmt = function
    | None ->
      Format_doc.fprintf fmt "?%d" !nb;
      incr nb;
    | Some arg ->
      Format_doc.fprintf fmt "(%a)" print_node arg
  in print_node fmt node

let rec prepare_signatures {problem; desc} =
  match desc with
  | NoSolution -> ()
  | Solved {tsol; _} ->
    ignore (Includemod.modtypes ~loc:Location.none ~mark:false
              problem.env tsol.mod_type problem.signature)
  | Working { solutions = _ :: _ :: _} -> ()
  | Working { current = Some (_, _, _, RecLimit _)} -> ()
  | Working { current = Some (_, _, _, Node (args, _))} ->
    List.iter (Option.iter prepare_signatures) args
  | Working { current = None} ->
    Misc.fatal_error "Invalid argument [Implicitmod.prepare_signatures]"

let print_it_holes_info fmt node =
  prepare_signatures node;
  let nb = ref 1 in
  let rec aux fmt {desc; problem} =
    match desc with
    | Solved _ -> ()
    | NoSolution ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_holes_info]"
    | Working { solutions = sol1 :: sol2 :: _; _ } ->
      Format_doc.fprintf fmt
        "@[<1>@[<2>?%d awaited an argument of signature @ %a@] @ \
          It can be filled by either @ %a @ or @ %a.@]\n"
          !nb
          Printtyp.Doc.modtype problem.signature
          Pprintast.Doc.module_expr sol1.psol
          Pprintast.Doc.module_expr sol2.psol;
      incr nb;
    | Working { current = Some (name, _, _, RecLimit _) } ->
      Format_doc.fprintf fmt
        "?%d could be filled with a new recursive call to %s @ \
         with no termination guaranty.\n"
          !nb name;
      incr nb;
    | Working { current = Some (_, _, _, Node ([], _))} ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_holes_info]"
    | Working { current = Some (_, _, _, Node (args, _))} ->
      List.iter (aux_arg fmt) args
    | Working { solutions = _; current = None; next = _} ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_holes_info]"
  and aux_arg fmt = function
    | None ->
      Format_doc.fprintf fmt
        "@[<2>?%d can be filled by \"()\" which is ambiguous with itself.@]\n"
          !nb;
      incr nb;
    | Some arg -> aux fmt arg
  in aux fmt node

let solution_is_still_valid problem {psol = _; tsol} =
  let snap = Btype.snapshot () in
  try
    ignore (Includemod.modtypes ~loc:Location.none ~mark:false
                    problem.env tsol.mod_type problem.signature);
    Btype.backtrack snap;
    true
  with Includemod.Error _ | Ctype.Unify _ -> Btype.backtrack snap; false

let rec prepare_args_for_refine = function
  | [] -> ()
  | Some {problem; desc = Solved sol} :: tl ->
    ignore (Includemod.modtypes ~loc:Location.none ~mark:false
                  problem.env sol.tsol.mod_type problem.signature);
    prepare_args_for_refine tl
  | _ :: tl -> prepare_args_for_refine tl

let prepare_argument : Env.t * Types.module_type -> implicit_inference =
  fun (env, mty) ->
    let nargs, sg = get_sig env 0 mty in
    let next = Env.find_structures sg env in
    let next = Misc.Stdlib.String.Map.to_seq next in
    {
      problem = {signature = mty; nargs; env };
      desc = Working { solutions = []; current = None; next }
    }

let type_module = ref (fun _ _ -> assert false)

let build_solution ~loc env name args =
  let rec build_mexp me = function
    | [] -> me
    | Some { desc = Solved sol} :: tl ->
      build_mexp
        { pmod_desc = Pmod_apply (me, sol.psol);
          pmod_loc = loc; pmod_attributes = [] }
        tl
    | _ -> assert false (* Should not happen *)
  in
  let functor_mexp =
    { pmod_desc = Pmod_ident {txt = Lident name; loc};
      pmod_loc = loc; pmod_attributes = [] }
  in
  let psol = build_mexp functor_mexp args in
  let tsol, _ = !type_module env psol in
  { psol; tsol }

let rec compute_nb_unsolved acc = function
  | [] -> acc
  | Some {desc = Solved _} :: tl -> compute_nb_unsolved acc tl
  | (Some {desc = Working _} | None) :: tl -> compute_nb_unsolved (acc + 1) tl
  | Some {desc = NoSolution} :: _ -> raise Not_found

let rec refine_solution ~loc trace {problem; desc} =
  match desc with
  | Solved s -> {problem; desc = Solved s}
  | NoSolution -> {problem; desc = NoSolution}
  | Working { solutions; current; next } ->
    let solutions =
      List.filter (solution_is_still_valid problem) solutions
    in
    if match solutions with _ :: _ :: _ -> true | _ -> false
    then begin
      {problem; desc = Working {solutions; current; next }}
    end else begin
      let prev_trace = trace in
      match current with
      | None ->
        begin match filter_identifiers ~loc trace problem next with
          | Some (name, _, _, Node (args, 0)), next ->
            let solutions = match build_solution ~loc problem.env name args with
              | sol -> sol :: solutions
              | exception (Includemod.Error _ | Includemod.Apply_error _
                    | Ctype.Unify _) ->
                solutions
            in
            let desc = Working { solutions; current = None; next } in
            refine_solution ~loc prev_trace {problem; desc}
          | None, next when Seq.is_empty next ->
            begin match solutions with
              | [] -> {problem; desc = NoSolution}
              | [sol] -> {problem; desc = Solved sol}
              | _ :: _ :: _ -> assert false (* Should not happen *)
            end
          | None, _ -> assert false (* Should not happen *)
          | current, next ->
            {problem; desc = Working { solutions; current; next}}
        end
      | Some (name, local_env, mty, Node (arguments, nb_unsolved)) ->
        begin
          let snap = Btype.snapshot () in
          match Includemod.modtypes ~loc:Location.none ~mark:false
                  local_env mty problem.signature
          with
          | exception (Ctype.Unify _ | Includemod.Error _) ->
            Btype.backtrack snap;
            let desc = Working { solutions; current = None; next } in
            refine_solution ~loc prev_trace {problem; desc}
          | _ ->
            let trace =
              match
                FuncOrder.update_map problem.env trace name problem.signature
              with
              | Some trace -> trace
              | None -> assert false
            in
            let arguments =
              refine_solution_list ~loc trace arguments nb_unsolved
            in
            Btype.backtrack snap;
            begin match arguments with
              | Some (args, 0) ->
                let solutions =
                  match build_solution ~loc problem.env name args with
                  | sol -> sol :: solutions
                  | exception (Includemod.Error _ | Includemod.Apply_error _
                            | Ctype.Unify _) ->
                    solutions
                in
                let desc = Working { solutions; current = None; next } in
                refine_solution ~loc prev_trace {problem; desc}
              | Some (args, nb_unsolved) ->
                let current =
                  Some (name, local_env, mty, Node (args, nb_unsolved))
                in
                { problem; desc = Working {solutions; current; next}}
              | None -> {problem; desc = NoSolution}
            end
          end
      | Some (name, local_env, mty, RecLimit params) ->
        begin
          let snap = Btype.snapshot () in
          match Includemod.modtypes ~loc:Location.none ~mark:false
                  local_env mty problem.signature
          with
          | exception (Ctype.Unify _ | Includemod.Error _) ->
            Btype.backtrack snap;
            let desc = Working { solutions; current = None; next } in
            refine_solution ~loc prev_trace {problem; desc}
          | _ ->
            match
              FuncOrder.update_map problem.env trace name problem.signature
            with
            | None ->
              Btype.backtrack snap;
              {problem; desc = Working {solutions; current; next}}
            | Some trace ->
              let opened_node, next =
                open_node ~loc snap trace problem name local_env mty params next
              in
              begin match opened_node with
              | Some (name, _, _, Node (args, 0)) ->
                let solutions =
                  match build_solution ~loc problem.env name args with
                  | sol -> sol :: solutions
                  | exception (Includemod.Error _ | Includemod.Apply_error _
                            | Ctype.Unify _) ->
                    solutions
                in
                let desc = Working { solutions; current = None; next } in
                refine_solution ~loc prev_trace {problem; desc}
              | None when Seq.is_empty next ->
                begin match solutions with
                  | [] -> {problem; desc = NoSolution}
                  | [sol] -> {problem; desc = Solved sol}
                  | _ :: _ :: _ -> assert false (* Should not happen *)
                end
              | None -> assert false (* Should not happen *)
              | _ ->
                {problem;
                 desc = Working { solutions; current = opened_node; next}}
              end
        end
    end
and refine_solution_list ~loc trace arguments nb_unsolved =
  match prepare_args_for_refine arguments with
  | () ->
    begin
      let arguments =
        List.map (Option.map (refine_solution ~loc trace)) arguments
      in
      match compute_nb_unsolved 0 arguments with
      | nb_unsolved' ->
        if nb_unsolved' < nb_unsolved
        then refine_solution_list ~loc trace arguments nb_unsolved'
        else Some (arguments, nb_unsolved')
      | exception Not_found -> None
    end
  | exception (Ctype.Unify _ | Includemod.Error _)  -> None
and filter_identifiers ~loc trace problem next =
  match Seq.uncons next with
  | None -> None, Seq.empty
  | Some ((name, path), rest) ->
    let mdecl =
      Env.find_strengthened_module ~aliasable:false path problem.env
    in
    match extract_function problem.env problem.nargs mdecl with
    | None -> filter_identifiers ~loc trace problem rest
    | Some (arguments, env_result, result) ->
      let snap = Btype.snapshot () in
      match
        Includemod.modtypes ~loc ~mark:false env_result result problem.signature
      with
      | exception (Includemod.Error _ | Ctype.Unify _) ->
        Btype.backtrack snap;
        filter_identifiers ~loc trace problem rest
      | _ ->
          match FuncOrder.update_map problem.env trace name problem.signature with
          | None ->
            Btype.backtrack snap;
            Some (name, env_result, result, RecLimit arguments), rest
          | Some trace ->
              open_node ~loc snap trace problem name env_result result
                arguments rest
and open_node ~loc snap trace problem name local_env mty arguments rest =
  let args = List.rev_map (Option.map prepare_argument) arguments in
  match refine_solution_list ~loc trace args (List.length args) with
  | None ->
    Btype.backtrack snap;
    filter_identifiers ~loc trace problem rest
  | Some (args, nb_unsolved) ->
    Btype.backtrack snap;
    Some (name, local_env, mty, Node (args, nb_unsolved)), rest

let infer ~loc env mty =
  let node = prepare_argument (env, mty) in
  let node = refine_solution ~loc FuncOrder.empty node in
  match node.desc with
  | Solved {psol; _} -> psol
  | _ ->
    raise (ImplicitError (loc, node))

(* Error report *)
open Printtyp.Doc

let report_implicit_error ~loc tree =
  if tree.desc = NoSolution
  then
    Location.errorf ~loc
        "@[<v>@[<2>Inference of signature %a@]@ \
          failed as no solution was found.@]"
          modtype tree.problem.signature
  else
    Location.errorf ~loc
        "@[<v>@[<2>Inference of signature %a@]@ \
          failed because inference could not make@ \
          any more progress. @ Final state was :@ %a.\n%a@]"
          modtype tree.problem.signature
          print_it_with_holes tree
          print_it_holes_info tree

let () =
  Location.register_error_of_exn
    (function
      | ImplicitError ((loc, tree)) ->
          Some (report_implicit_error ~loc tree)
      | _ -> None)
