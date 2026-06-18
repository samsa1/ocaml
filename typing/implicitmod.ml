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

module Constraints = Implicitmod_constraints

module Includemod = struct
  include Includemod
  let modtypes_collect_constraint ~loc ~mark env_result
          result problem_signature =
      Profile.record_call ~accumulate:true "collect_constraint" @@
        fun () -> modtypes_collect_constraint ~loc ~mark
                      env_result result problem_signature

  let approx_modtypes env ~constraints mty1 mty2 =
    !Clflags.no_imp_filter2 || approx_modtypes env ~constraints mty1 mty2
end

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
    | Some ty -> type_expr env 100 ty

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
    | Mty_functor (Unit, mty2) -> module_type env mty2
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

  let update_map = Profile.record ~accumulate:true "update_map" update_map
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
  | Mty_functor (Named (_, n, arg_ty) as param, mty) ->
    let env = match n with
      | None -> env
      | Some id ->
        Env.add_module ~noalias:true id Mp_present IILocal arg_ty env
    in extract_arguments env (param :: args) mty
  | Mty_ident _ ->
      failwith "NYI : Inference with abstract signatures"
  | Mty_alias _ -> assert false

type extracted_arg =
  | EA_Unit
  | EA_Arg of Ident.t * Env.t * Types.module_type

let rec prepare_args d env args =
  match args with
  | [] -> ([], env, Subst.identity)
  | Unit :: rest ->
      let args, env, subst = prepare_args d env rest in
      (EA_Unit :: args, env, subst)
  | Named (_, id, arg_ty) :: rest ->
      let args, env, subst = prepare_args d env rest in
      (* let arg_ty = open_module_type env arg_ty in *)
      let oid, env, subst = match id with
        | None ->
          let id' = Ident.create_flex ~scope:(Ctype.get_current_level ())
                ("?" ^ string_of_int d ^ "?_?")
          in
          id', env, subst
        | Some id ->
          let id' = Ident.create_flex ~scope:(Ctype.get_current_level ())
                        ("?" ^ string_of_int d ^ "?" ^ Ident.name id)
          in
          id',
          Env.add_module ~noalias:true id' Mp_present IILocal arg_ty env,
          Subst.add_module id (Pident id') subst
      in
      (EA_Arg (oid, env, Subst.modtype Keep subst arg_ty) :: args, env, subst)

let extract_function search_depth env depth mty =
  let rec aux d args mty =
    if d = 0
    then
      let (args, env, subst) = prepare_args search_depth env args in
      Some (args, env, Subst.modtype Keep subst mty)
    else match args with
      | [] -> None
      | arg :: rest -> aux (d - 1) rest (Mty_functor (arg, mty))
  in
  let (args, mty) = extract_arguments env [] mty in
  aux depth args mty

let extract_function =
  Profile.record ~accumulate:true "extract function" extract_function

let rec get_sig env depth mty =
    match Env.scrape_alias env mty with
    | Mty_signature sg -> (depth, sg)
    | Mty_functor (_, mty) -> get_sig env (depth + 1) mty
    | _ -> Misc.fatal_error "infer_implicit"

type implicit_inference_solution = {
  psol : Parsetree.module_expr;
  tsol : Typedtree.module_expr;
  path : Path.t;
  constraints : Constraints.t;
}

type problem = {
  id : Ident.t;
  modtype : Types.module_type;
  env : Env.t;
  signature : Types.module_type;
  nargs : int;
}

type implicit_inference = {
  problem : problem;
  desc : implicit_inference_desc;
}
and args_status =
  | RecLimit of extracted_arg list
  | Node of recursive_arg list * int
and recursive_arg =
  | Arg of implicit_inference
  | Unit
and implicit_inference_desc =
  | Solved of implicit_inference_solution
  | Working of {
      solutions : implicit_inference_solution list;
      current : current_status option;
      next : (Misc.modname * Path.t) Seq.t;
    }
  | NoSolution
and current_status = {
  name : Misc.modname;
  path : Path.t;
  local_env : Env.t;
  ret_mty : Types.module_type;
  args_status : args_status;
  constraints : Constraints.t;
}

exception ImplicitError of Location.t * implicit_inference

let map_recursive_arg f = function
  | Arg prob -> Arg (f prob)
  | Unit -> Unit

let rec collect_all_constraints env cstrs = function
  | Arg { desc = Solved sol } :: tl ->
    collect_all_constraints env
      (Constraints.merge env sol.constraints cstrs)
      tl
  | Arg _ :: tl | Unit :: tl ->
    collect_all_constraints env cstrs tl
  | [] -> cstrs

let print_it_with_holes fmt node =
  let nb = ref 1 in
  let rec print_node fmt {desc; _} =
    match desc with
    | Solved {psol; _} ->
      Pprintast.Doc.module_expr fmt psol
    | NoSolution ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_with_holes]"
    | Working { solutions = _ :: _ :: _; _ }
    | Working { current = Some { args_status = RecLimit _ } } ->
      Format_doc.fprintf fmt "?%d" !nb;
      incr nb;
    | Working { current = Some { args_status = Node ([], _); _ }} ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_with_holes]"
    | Working { current = Some {name; args_status = Node (args, _); _}} ->
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
    | Unit ->
      Format_doc.fprintf fmt "?%d" !nb;
      incr nb;
    | Arg arg ->
      Format_doc.fprintf fmt "(%a)" print_node arg
  in print_node fmt node

let print_it_holes_info fmt node =
  let nb = ref 1 in
  let rec aux ctxt_cstrts fmt {desc; problem} =
    match desc with
    | Solved _ -> ()
    | NoSolution ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_holes_info]"
    | Working { solutions = sol1 :: sol2 :: _; _ } ->
      Format_doc.fprintf fmt
        "@[<1>@[<2>?%d awaited an argument of signature @ %a@] @ \
          It can be filled by either @ %a @ or @ %a.@]\n%a%a"
          !nb
          Printtyp.Doc.modtype problem.modtype
          Pprintast.Doc.module_expr sol1.psol
          Pprintast.Doc.module_expr sol2.psol
          Constraints.print (Constraints.merge problem.env ctxt_cstrts sol1.constraints)
          Constraints.print (Constraints.merge problem.env ctxt_cstrts sol2.constraints);
      incr nb;
    | Working { current = Some {name; args_status = RecLimit _; _} } ->
      Format_doc.fprintf fmt
        "?%d could be filled with a new recursive call to %s @ \
         with no termination guaranty.\n"
          !nb name;
      incr nb;
    | Working { current = Some { args_status = Node ([], _) }} ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_holes_info]"
    | Working { current = Some { args_status = Node (args, _); local_env; constraints}} ->
      let local_cstrts =
        Constraints.merge local_env ctxt_cstrts constraints
      in
      let () =
        Format.eprintf "%a"
          (Format_doc.compat Constraints.print)
          local_cstrts
      in
      List.iter (aux_arg local_cstrts fmt) args
    | Working { solutions = _; current = None; next = _} ->
      Misc.fatal_error "Invalid argument [Implicitmod.print_it_holes_info]"
  and aux_arg ctxt_cstrts fmt = function
    | Unit ->
      Format_doc.fprintf fmt
        "@[<2>?%d can be filled by \"()\" which is ambiguous with itself.@]\n"
          !nb;
      incr nb;
    | Arg arg -> aux ctxt_cstrts fmt arg
  in aux Constraints.empty fmt node

let solution_is_still_valid problem ctxt_constraints {constraints; psol = _; path = _; _}
=
  let local_ctxt = Constraints.merge problem.env ctxt_constraints constraints in
  not (Constraints.has_error problem.env local_ctxt)

let prepare_argument id env modtype : implicit_inference =
  let mty = Mtype.strengthen ~aliasable:false env modtype (Pident id)
  in
  let nargs, sg = get_sig env 0 mty in
  let next = Env.find_structures sg env in
  let next = Misc.Stdlib.String.Map.to_seq next in
  {
    problem = {id; modtype; signature = mty; nargs; env };
    desc = Working { solutions = []; current = None; next }
  }

let prepare_argument =
  Profile.record ~accumulate:true "prepare_argument" prepare_argument

let prepare_extracted_argument = function
  | EA_Arg (oid, env, mty) -> Arg (prepare_argument oid env mty)
  | EA_Unit -> Unit

let type_module = ref (fun _ _ -> assert false)
let type_one_application_to_path = ref (fun ~loc:_ _ _ _ _ -> assert false)

let build_solution ~loc {id; env; signature} name path args =
  let snap = Btype.snapshot () in
  let rec build_mexp pme path tme = function
    | [] ->
      if not (Includemod.approx_modtypes env ~constraints:Constraints.empty tme.Typedtree.mod_type signature)
      then begin
        Btype.backtrack snap;
        None
      end else begin
        match
          Includemod.modtypes_collect_constraint ~loc ~mark:false env
              tme.Typedtree.mod_type signature
        with
        | constraints ->
          Btype.backtrack snap;
          let constraints = Constraints.of_tmp env constraints in
          Some {
            psol = pme;
            tsol = tme;
            path = Env.normalize_module_path (Some Location.none) env path;
            constraints =
              Constraints.add_path_eq env Constraints.Module
                (Pident id) path constraints;
          }
        | exception (Includemod.Error _ | Ctype.Unify _) ->
          Btype.backtrack snap;
          None
      end
    | Arg { desc = Solved sol} :: tl ->
      begin match
          !type_one_application_to_path ~loc:Location.none env
            tme sol.path sol.tsol
        with
        | Some tsol ->
          build_mexp
            { pmod_desc = Pmod_apply (pme, sol.psol);
              pmod_loc = loc; pmod_attributes = [] }
            (Path.Papply (path, sol.path))
            tsol
            tl
        | None
        | exception (Includemod.Error _ | Includemod.Apply_error _
          | Ctype.Unify _) ->
            None
      end
    | _ -> assert false (* Should not happen *)
  in
  let functor_mexp =
    { pmod_desc = Pmod_ident {txt = Lident name; loc};
      pmod_loc = loc; pmod_attributes = [] }
  in
  build_mexp functor_mexp path (fst (!type_module env functor_mexp)) args

let build_solution ~loc prob name path args =
  Profile.record_call ~accumulate:true "build solution" @@
    fun () -> build_solution ~loc prob name path args

exception NoSol

let rec compute_nb_unsolved acc = function
  | [] -> acc
  | Arg {desc = Solved _} :: tl -> compute_nb_unsolved acc tl
  | (Arg {desc = Working _} | Unit) :: tl -> compute_nb_unsolved (acc + 1) tl
  | Arg {desc = NoSolution} :: _ -> raise NoSol

let rec remove_duplicate_sols : implicit_inference_solution list -> _ = function
  | sol1 :: sol2 :: tl when Path.same sol1.path sol2.path ->
    remove_duplicate_sols (sol1 :: tl)
  | sols -> sols

let rec build_path path = function
  | [] -> Some path
  | EA_Unit :: _ -> None
  | EA_Arg (id, _, _) :: tl -> build_path Path.(Papply (path, Pident id)) tl

let rec refine_solution d ~loc trace ctxt_constraints {problem; desc} =
  match desc with
  | Solved s -> {problem; desc = Solved s}
  | NoSolution -> {problem; desc = NoSolution}
  | Working { solutions; current; next } ->
    let solutions =
      remove_duplicate_sols @@
        List.filter (solution_is_still_valid problem ctxt_constraints) solutions
    in
    if match solutions with _ :: _ :: _ -> true | _ -> false
    then begin
      {problem; desc = Working {solutions; current; next }}
    end else begin
      let prev_trace = trace in
      match current with
      | None ->
        begin
          match filter_identifiers d ~loc trace ctxt_constraints problem next with
          | Some {name; path; args_status = Node (args, 0); _}, next ->
            let solutions =
              match build_solution ~loc problem name path args with
              | Some sol -> sol :: solutions
              | None -> solutions
            in
            let desc = Working { solutions; current = None; next } in
            refine_solution d ~loc prev_trace ctxt_constraints {problem; desc}
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
      | Some {name; path; local_env; ret_mty; constraints;
              args_status = Node (arguments, nb_unsolved)} ->
        begin
          let snap = Btype.snapshot () in
          let local_constraints =
            Constraints.merge local_env ctxt_constraints constraints
          in
          if Constraints.has_error local_env local_constraints
          then begin
            Btype.backtrack snap;
            let desc = Working { solutions; current = None; next } in
            refine_solution d ~loc prev_trace ctxt_constraints {problem; desc}
          end else begin
            let trace =
              match
                FuncOrder.update_map problem.env trace name problem.signature
              with
              | Some trace -> trace
              | None -> assert false
            in
            let arguments =
              refine_solution_list (d + 1) ~loc local_env trace
                                    local_constraints arguments nb_unsolved
            in
            Btype.backtrack snap;
            begin match arguments with
              | Some (args, 0) ->
                let solutions =
                  match build_solution ~loc problem name path args with
                  | Some sol -> sol :: solutions
                  | None -> solutions
                in
                let desc = Working { solutions; current = None; next } in
                refine_solution d ~loc prev_trace ctxt_constraints {problem; desc}
              | Some (args, nb_unsolved) ->
                let current =
                  Some {name; path; local_env; ret_mty; constraints;
                        args_status = Node (args, nb_unsolved)}
                in
                { problem; desc = Working {solutions; current; next}}
              | None -> {problem; desc = NoSolution}
            end
          end
        end
      | Some {name; path; local_env; ret_mty; constraints;
              args_status = RecLimit params} ->
        begin
          let snap = Btype.snapshot () in
          let local_constraints =
            Constraints.merge local_env ctxt_constraints constraints
          in
          if Constraints.has_error local_env local_constraints
          then begin
            Btype.backtrack snap;
            let desc = Working { solutions; current = None; next } in
            refine_solution d ~loc prev_trace ctxt_constraints {problem; desc}
          end else begin
            match
              FuncOrder.update_map problem.env trace name problem.signature
            with
            | None ->
              Btype.backtrack snap;
              {problem; desc = Working {solutions; current; next}}
            | Some trace ->
              let opened_node, next =
                open_node d ~loc snap trace ctxt_constraints constraints problem
                  name path local_env ret_mty params next
              in
              begin match opened_node with
              | Some {name; args_status = Node (args, 0); _} ->
                let solutions =
                  match build_solution ~loc problem name path args with
                  | Some sol -> sol :: solutions
                  | None -> solutions
                in
                let desc = Working { solutions; current = None; next } in
                refine_solution d ~loc prev_trace ctxt_constraints {problem; desc}
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
    end
and refine_solution_list d ~loc env trace ctxt_constraints arguments nb_unsolved =
  (* match prepare_args_for_refine arguments with
  | () ->
    begin *)
      let local_constraints =
        collect_all_constraints env ctxt_constraints arguments
      in
      let arguments =
        List.map (map_recursive_arg (refine_solution d ~loc trace local_constraints)) arguments
      in
      match compute_nb_unsolved 0 arguments with
      | nb_unsolved' ->
        if nb_unsolved' < nb_unsolved
        then refine_solution_list d ~loc env trace ctxt_constraints arguments nb_unsolved'
        else Some (arguments, nb_unsolved')
      | exception NoSol ->
        None
    (* end
  | exception (Ctype.Unify _ | Includemod.Error _)  -> None *)
and filter_identifiers d ~loc trace ctxt_constraints problem next =
  match Seq.uncons next with
  | None -> None, Seq.empty
  | Some ((name, path), rest) ->
    let mdecl =
      Env.find_strengthened_module ~aliasable:false path problem.env
    in
    match extract_function d problem.env problem.nargs mdecl with
    | None ->
      filter_identifiers d ~loc trace ctxt_constraints problem rest
    | Some (_, env_result, result)
        when not (Includemod.approx_modtypes env_result ~constraints:ctxt_constraints result problem.signature) ->
      filter_identifiers d ~loc trace ctxt_constraints problem rest
    | Some (arguments, env_result, result) ->
      let snap = Btype.snapshot () in
      match
        Includemod.modtypes_collect_constraint ~loc ~mark:false env_result
          result problem.signature
      with
      | exception (Includemod.Error _ | Ctype.Unify _) ->
        Btype.backtrack snap;
        filter_identifiers d ~loc trace ctxt_constraints problem rest
      | constraints ->
        let constraints = Constraints.of_tmp env_result constraints in
        let constraints =
          match build_path path (List.rev arguments) with
          | None -> constraints
          | Some path ->
            Constraints.add_path_eq env_result Constraints.Module
              (Pident problem.id) path
              constraints
        in
        if Constraints.(has_error env_result (merge env_result ctxt_constraints constraints))
        then begin
          Btype.backtrack snap;
          filter_identifiers d ~loc trace ctxt_constraints problem rest
        end else begin
          match
            FuncOrder.update_map problem.env trace name problem.signature
          with
          | None ->
            Btype.backtrack snap;
            Some {name; path; local_env = env_result; ret_mty = result;
                  args_status = RecLimit arguments; constraints}, rest
          | Some trace ->
              open_node d ~loc snap trace ctxt_constraints constraints problem
                name path env_result result arguments rest
        end
and open_node d ~loc snap trace ctxt_constraints constraints problem name path
    local_env ret_mty arguments rest =
  let args = List.rev_map prepare_extracted_argument arguments in
  let local_constraints =
    Constraints.merge local_env ctxt_constraints constraints
  in
  match
    refine_solution_list (d + 1) ~loc local_env trace local_constraints args (List.length args)
  with
  | None ->
    Btype.backtrack snap;
    filter_identifiers d ~loc trace ctxt_constraints problem rest
  | Some (args, nb_unsolved) ->
    Btype.backtrack snap;
    Some {name; path; local_env; ret_mty; constraints;
          args_status = Node (args, nb_unsolved)},
      rest

let infer ~loc env mty =
  let scope = Ctype.get_current_level () in
  let node = prepare_argument (Ident.create_flex ~scope "?Y") env mty in
  let node =
    refine_solution 0 ~loc FuncOrder.empty Constraints.empty node
  in
  match node.desc with
  | Solved {psol; _} -> psol
  | _ ->
    raise (ImplicitError (loc, node))

let infer ~loc env mty =
  Profile.record_call ~accumulate:true "implicit"
    (fun () -> infer ~loc env mty)

(* Error report *)
open Printtyp.Doc

let report_implicit_error ~loc tree =
  if tree.desc = NoSolution
  then
    Location.errorf ~loc
        "@[<v>@[<2>Inference of signature %a@]@ \
          failed as no solution was found.@]"
          modtype tree.problem.modtype
  else
    Location.errorf ~loc
        "@[<v>@[<2>Inference of signature %a@]@ \
          failed because inference could not make@ \
          any more progress. @ Final state was :@ %a.\n%a@]"
          modtype tree.problem.modtype
          print_it_with_holes tree
          print_it_holes_info tree

let () =
  Location.register_error_of_exn
    (function
      | ImplicitError ((loc, tree)) ->
          Some (report_implicit_error ~loc tree)
      | _ -> None)
