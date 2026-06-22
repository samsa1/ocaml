(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*            Samuel Vivien, projet Cambium, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2026 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@warning "-69-37"]

type path_eq_kind =
  | Module
  | Type of int

(* type path_with_head = {
  path : Path.t;
  (* first : Ident.t; *)
} *)

type params = (Ident.t * Types.module_type) list

(* let build_path_pair eq_kind pp_params ~rigid:pp_rigid ~flex:pp_flex =
  let rec filter_params = function
  | [] -> []
  | (id, _) as hd :: tl ->
    let tl = filter_params tl in
    match tl with
    | [] ->
      if Path.exists_free [id] pp_rigid.path
          || Path.exists_free [id] pp_flex.path
      then
        [hd]
      else
        []
    | _ -> hd :: tl
  in
  {eq_kind; pp_params = filter_params pp_params; pp_rigid; pp_flex} *)

type path_operation =
  | Pop_dot of string
  | Pop_extra_ty of Path.extra_ty
  | Pop_apply of Path.t

let decompose_path p =
  let open Path in
  let rec aux acc = function
    | Pident id -> (id, acc)
    | Pdot (p, s) -> aux (Pop_dot s :: acc) p
    | Papply (pfun, parg) ->
      aux (Pop_apply parg :: acc) pfun
    | Pextra_ty (p, ety) -> aux (Pop_extra_ty ety :: acc) p
  in
  aux [] p

module EtyMap = Map.Make(struct
  type t = Path.extra_ty
  let compare x y =
    match x, y with
    | Path.Pext_ty, Path.Pext_ty -> 0
    | Path.Pext_ty, _ -> 1
    | _, Path.Pext_ty -> -1
    | Path.Pcstr_ty a, Path.Pcstr_ty b -> String.compare a b
end)

module SMap = Misc.Stdlib.String.Map

module ModId : sig
  type t = private int
  type _ map
  (* module Map : Map.S with type t = t *)

  val empty_map : 'a map

  val find : t -> 'a map -> 'a
  val add : 'a -> 'a map -> t * 'a map
  val update : t -> 'a -> 'a map -> 'a map
  val union : (t -> 'a -> 'a -> 'a option) -> 'a map -> 'a map -> 'a map
  (* val merge :
    (t -> 'a option -> 'a option -> 'a option) -> 'a map -> 'a map -> 'a map *)
  val iter : (t -> 'a -> unit) -> 'a map -> unit
  val exists : (t -> 'a -> bool) -> 'a map -> bool
end = struct
  type t = int
  module Map = Map.Make(Int)

  type 'a map = 'a Map.t

  let empty_map = Map.empty

  let r = ref 0

  let add el m =
    let id = !r in
    incr r;
    (id, Map.add id el m)

  let find = Map.find
  let update = Map.add
  let union = Map.union
  (* let merge = Map.merge *)
  let iter = Map.iter
  let exists = Map.exists
end

(* type equiv_path =
  | EPident of Ident.t (* Always rigid *)
  | EPapply of equiv_path * equiv_path
  | EPapply_id of equiv_path * (ModId.t * Path.t)
  | EPdot of equiv_path * string
  | EPety of equiv_path * Path.extra_ty *)

type constraint_eq =
  | CE_PathR of Path.t
  | CE_PathF of ModId.t * (Path.t * path_operation list) option
  | CE_Type of Types.type_expr list * Types.type_expr

type path_pair = {
  eq_kind : path_eq_kind;
  pp_params : params;
  pp_instances : Path.t option list list;
  pp_left : Path.t * path_operation list;
  pp_right : constraint_eq;
}

type module_desc =
  | Alias of ModId.t
  | BaseType of int * (Types.type_expr list * Types.type_expr) list
  | Mod
  (* | Equalities of path_pair list *)
  | App of {
      static_apps : ModId.t Path.Map.t;
      quantified_apps : path_pair list;
    }
  | Projections of ModId.t SMap.t
  | ExtraProjs of ModId.t EtyMap.t

type module_info = {
  mi_path : Path.t option;
  mi_desc : module_desc;
}

type t_inner = {
  flex_heads : ModId.t Ident.Map.t;
  data : module_info ModId.map;
}

type t =
  | HasContradiction
  | Constraints of t_inner

let empty = Constraints {
  flex_heads = Ident.Map.empty;
  data = ModId.empty_map;
}

(* let to_path_with_head path =
  { path = path; first = Path.first path } *)


let expand_head_rigid = ref (fun _ _ -> assert false)

let type_expr_printer = ref (fun _ _ -> assert false)

module Pp = struct
  let print_params fmt params =
    Format_doc.fprintf fmt "[%a]"
      (Format_doc.pp_print_list
        (fun fmt (id, _) -> Format_doc.pp_print_string fmt (Ident.name id)))
      params

  (* let print_path_pair fmt {eq_kind; pp_params; pp_rigid; pp_flex} =
    Format_doc.fprintf fmt "@[<hov2>%a@ %a@ =%s@ %a@]"
      print_params pp_params
      Path.print pp_rigid.path
      (match eq_kind with Module -> "m" | Type -> "t")
      Path.print pp_flex.path *)

  let print_ety fmt = function
    | Path.Pext_ty -> Format_doc.fprintf fmt "[%%ext]"
    | Path.Pcstr_ty s -> Format_doc.fprintf fmt "[%%ext %s]" s

  let pp_sep fmt () = Format_doc.fprintf fmt ", "

  let print_cstrs fmt (tyl, ty) =
    Format_doc.fprintf fmt "[%a => %a]"
      (Format_doc.pp_print_list ~pp_sep !type_expr_printer) tyl
      !type_expr_printer ty

  let print_path_op fmt = function
    | Pop_dot s | Pop_extra_ty (Pcstr_ty s) ->
        Format_doc.fprintf fmt ".%s" s
    | Pop_apply parg -> Format_doc.fprintf fmt "(%a)" Path.print parg
    | Pop_extra_ty Pext_ty -> ()

  let print_mi_desc fmt = function
    | Mod ->
      Format_doc.fprintf fmt "Mod"
    | BaseType (0, [([], ty)]) ->
      Format_doc.fprintf fmt "=t %a" !type_expr_printer ty
    | BaseType (_, cstrs) ->
      Format_doc.fprintf fmt "=? %a"
        (Format_doc.pp_print_list ~pp_sep print_cstrs) cstrs
    | Alias i ->
      Format_doc.fprintf fmt "= %d" (i :> int)
    (* | Equalities pairs ->
      Format_doc.fprintf fmt "@[<hov2>%a@]"
        (Format_doc.pp_print_list print_path_pair) pairs *)
    | Projections projs ->
      let print_proj fmt (s, cstrs) =
        Format_doc.fprintf fmt "@[<hov2>field %s ->@ %d@]"
          s (cstrs : ModId.t :> int)
      in
      Format_doc.fprintf fmt "@[<hov2>%a@]"
        (Format_doc.pp_print_list print_proj) (SMap.to_list projs)
    | ExtraProjs projs ->
      let print_proj fmt (ety, cstrs) =
        Format_doc.fprintf fmt "@[<hov2>field %a ->@ %d@]"
          print_ety ety (cstrs : ModId.t :> int)
      in
      Format_doc.fprintf fmt "@[<hov2>%a@]"
        (Format_doc.pp_print_list print_proj) (EtyMap.to_list projs)
    | App { static_apps; quantified_apps } ->
      let print_app fmt (parg, cstrs) =
        Format_doc.fprintf fmt "@[<hov2>app %a ->@ %d@]"
          Path.print parg (cstrs : ModId.t :> int)
      in
      let print_qapp fmt pp_eq =
        match pp_eq.pp_right with
        | CE_PathR p2 ->
          Format_doc.fprintf fmt "@[<hov2>%a@ ?(%a)%a@ =%s@ %a@]"
            print_params pp_eq.pp_params
            Path.print (fst pp_eq.pp_left)
            (Format_doc.pp_print_list print_path_op) (snd pp_eq.pp_left)
            (match pp_eq.eq_kind with Module -> "m" | Type _ -> "t")
            Path.print p2
        | CE_PathF (id_r, Some (parg_r, ops_r)) ->
          Format_doc.fprintf fmt "@[<hov2>%a@ ?(%a)%a@ =%s@ %d(%a)%a@]"
            print_params pp_eq.pp_params
            Path.print (fst pp_eq.pp_left)
            (Format_doc.pp_print_list print_path_op) (snd pp_eq.pp_left)
            (match pp_eq.eq_kind with Module -> "m" | Type _ -> "t")
            (id_r :> int)
            Path.print parg_r
            (Format_doc.pp_print_list print_path_op) ops_r
        | CE_PathF (id_r, None) ->
          Format_doc.fprintf fmt "@[<hov2>%a@ ?(%a)%a@ =%s@ %d@]"
            print_params pp_eq.pp_params
            Path.print (fst pp_eq.pp_left)
            (Format_doc.pp_print_list print_path_op) (snd pp_eq.pp_left)
            (match pp_eq.eq_kind with Module -> "m" | Type _ -> "t")
            (id_r :> int)
        | CE_Type ([], ty) ->
          Format_doc.fprintf fmt "@[<hov2>%a@ ?(%a)%a@ =%s@ %a@]"
            print_params pp_eq.pp_params
            Path.print (fst pp_eq.pp_left)
            (Format_doc.pp_print_list print_path_op) (snd pp_eq.pp_left)
            (match pp_eq.eq_kind with Module -> "m" | Type _ -> "t")
            !type_expr_printer ty
        | CE_Type (_tyl, _ty) ->
          Format_doc.fprintf fmt "@[<hov2>%a@ ?(%a)%a@ =%s@ ?@]"
            print_params pp_eq.pp_params
            Path.print (fst pp_eq.pp_left)
            (Format_doc.pp_print_list print_path_op) (snd pp_eq.pp_left)
            (match pp_eq.eq_kind with Module -> "m" | Type _ -> "t")
      in
      Format_doc.fprintf fmt "@[<hov2>%a@ %a@]"
        (Format_doc.pp_print_list print_app) (Path.Map.to_list static_apps)
        (Format_doc.pp_print_list print_qapp) quantified_apps

  let pp_info fmt info =
    Format_doc.fprintf fmt "@[{p = %a;@ d = %a}@]"
      (Format_doc.pp_print_option Path.print) info.mi_path
      print_mi_desc info.mi_desc

  let pp_data fmt data =
    let aux fmt mod_id info =
      Format_doc.fprintf fmt "%d =>@ %a\n"
        (mod_id : ModId.t :> int) pp_info info
    in
    Format_doc.fprintf fmt "@[<hov>data = %a@]"
      (fun fmt -> ModId.iter (aux fmt)) data

  let pp_flex_heads fmt flex_heads =
    let aux fmt i mod_id =
      Format_doc.fprintf fmt "%s =>@ %d\n"
        (Ident.name i) (mod_id : ModId.t :> int)
    in
    Format_doc.fprintf fmt "@[<hov>flex_heads = %a@]"
      (fun fmt -> Ident.Map.iter (aux fmt)) flex_heads

  let print_inner fmt eqs =
    Format_doc.fprintf fmt "@[<hov2>{%a;@ %a}@]"
      pp_flex_heads eqs.flex_heads
      pp_data eqs.data
end

let print fmt eqs =
  match eqs with
  | Constraints eqs -> Pp.print_inner fmt eqs
  | HasContradiction -> Format_doc.fprintf fmt "Absurd"

let print fmt eqs =
  if false then Format_doc.fprintf fmt "%a\n" print eqs else ()

let rec add_ops_to_path p = function
  | [] -> p
  | Pop_dot s :: ops -> add_ops_to_path (Path.Pdot (p, s)) ops
  | Pop_apply parg :: ops -> add_ops_to_path (Path.Papply (p, parg)) ops
  | Pop_extra_ty ety :: ops -> add_ops_to_path (Path.Pextra_ty (p, ety)) ops

let rec build_normalized_path prefix env eqs ops id =
  let info = ModId.find id eqs.data in
  let prefix =
    match info.mi_path with
    | Some p -> p
    | None -> prefix
  in
  match info.mi_desc, ops with
  | _, [] -> prefix
  | Alias id, _ -> build_normalized_path prefix env eqs ops id
  | BaseType _, _ :: _ -> assert false
  | (Mod (*| Equalities _*)), _ -> add_ops_to_path prefix ops
  | Projections projs, Pop_dot s :: ops ->
    let prefix = Path.Pdot (prefix, s) in
    begin match SMap.find s projs with
    | id' -> build_normalized_path prefix env eqs ops id'
    | exception Not_found ->
      add_ops_to_path prefix ops
    end
  | ExtraProjs projs, Pop_extra_ty ety :: ops ->
    let prefix = Path.Pextra_ty (prefix, ety) in
    begin match EtyMap.find ety projs with
    | id' ->
      build_normalized_path prefix env eqs ops id'
    | exception Not_found ->
      add_ops_to_path prefix ops
    end
  | App { static_apps }, Pop_apply parg :: ops ->
    let prefix = Path.Papply (prefix, parg) in
    let parg = normalize_module_path env eqs parg in
    begin match Path.Map.find parg static_apps with
    | constraints ->
      build_normalized_path prefix env eqs ops constraints
    | exception Not_found ->
      add_ops_to_path prefix ops
    end
  | Projections _, _ | _, Pop_dot _ :: _ -> assert false
  | ExtraProjs _, _ | _, Pop_extra_ty _ :: _ -> assert false
and normalize_module_path env eqs p =
  Env.normalize_module_path (Some Location.none) env (path_subst_map env eqs p)
and path_subst_map env eqs p =
  if Ident.rigid (Path.first p) then
    let open Path in
    let rec map = function
      | Pident id -> Pident id
      | Papply (pfun, parg) ->
          Papply (map pfun, normalize_module_path env eqs parg)
      | Pdot (p, s) -> Pdot (map p, s)
      | Pextra_ty (p, ety) -> Pextra_ty (map p, ety)
    in map p
  else
    let i, ops = decompose_path p in
    match Ident.Map.find i eqs.flex_heads with
    | constraints ->
      build_normalized_path (Path.Pident i) env eqs ops constraints
    | exception Not_found -> p

let rec normalize_type_path env p =
  (* let p' = path_subst_map env eqs p in *)
  match Env.find_type_expansion p env with
  | (params, ty, _) ->
    begin
      assert (params = []);
      match Types.get_desc ty with
      | Tconstr (p, [], _) ->
        normalize_type_path env p
      | _ ->
        Env.normalize_type_path (Some Location.none) env p
    end
  | exception Not_found ->
    Env.normalize_type_path (Some Location.none) env p

(* let rec split_flex_flex env i p still_flex flexibility_changed = function
  | [] -> still_flex, flexibility_changed
  | (k, params, p1, p2) :: tl ->
    let still_flex, flexibility_changed =
      if Ident.same p1.first i || Ident.same p2.first i then
        still_flex, (k, params, p1.path, p2.path) :: flexibility_changed
      else
        (k, params, p1, p2) :: still_flex, flexibility_changed
    in
    split_flex_flex env i p still_flex flexibility_changed tl

let rec split_rigid_flex env i p still_flex flexibility_changed = function
  | [] -> still_flex, flexibility_changed
  | {eq_kind; pp_params; pp_rigid; pp_flex} :: tl ->
    let still_flex, flexibility_changed =
      if Ident.same pp_flex.first i then
        still_flex,
          (eq_kind, pp_params, pp_rigid.path, pp_flex.path)
            :: flexibility_changed
      else
        {eq_kind; pp_params; pp_rigid; pp_flex} :: still_flex,
          flexibility_changed
    in
    split_rigid_flex env i p still_flex flexibility_changed tl

let rec split_path_type_eq env i p still_flex flexibility_changed = function
  | [] -> still_flex, flexibility_changed
  | PathEqType {params; path_flex; tyl; ty2 } :: tl ->
    let still_flex, flexibility_changed =
      if Ident.same path_flex.first i then
        still_flex, (params, path_flex.path, tyl, ty2) :: flexibility_changed
      else
        PathEqType {params; path_flex; tyl; ty2 } :: still_flex,
          flexibility_changed
    in
    split_path_type_eq env i p still_flex flexibility_changed tl
  | PathEqPath {params; path_flex1; tyl1; path_flex2; tyl2 } :: tl ->
    let still_flex, flexibility_changed =
      if Ident.same path_flex1.first i || Ident.same path_flex2.first i then
        let ty =
          Btype.newgenty (Tconstr (path_flex2.path, tyl2, ref Types.Mnil))
        in
        still_flex, (params, path_flex1.path, tyl1, ty) :: flexibility_changed
      else
        PathEqPath {params; path_flex1; tyl1; path_flex2; tyl2 } :: still_flex,
          flexibility_changed
    in
    split_path_type_eq env i p still_flex flexibility_changed tl *)

(* type update_constraints_result =
  | UCR_Contradiction
  | UCR_Ok of {
    constraints : identifier_constraint
  } *)

(* let rec build_constraints data prefix ops path_pair =
  let mi_desc, mi_kind, data =
    match ops with
    | [] ->
      if path_pair.pp_params = [] then
        Solved, path_pair.eq_kind, data
      else
        Equalities [path_pair], path_pair.eq_kind, data
    | Pop_apply parg :: ops ->
      if Path.exists_free (List.map fst path_pair.pp_params) parg then
        App { static_apps = Path.Map.empty; quantified_apps = [path_pair] },
          Module,
          data
      else
        let ret_id, data =
          build_constraints data (Path.Papply (prefix, parg)) ops path_pair
        in
        let static_apps = Path.Map.singleton parg ret_id in
        App { static_apps; quantified_apps = [] }, Module, data
    | Pop_dot s :: ops ->
      let proj_id, data =
        build_constraints data (Path.Pdot (prefix, s)) ops path_pair
      in
      let projs = SMap.singleton s proj_id in
      Projections projs, Module, data
    | Pop_extra_ty ety :: ops ->
      let proj_id, data =
        build_constraints data (Path.Pextra_ty (prefix, ety)) ops path_pair
      in
      let projs = EtyMap.singleton ety proj_id in
      ExtraProjs projs, Module, data
  in
  ModId.add { mi_path = prefix; mi_desc; mi_kind } data *)

let path_op_map_path f = function
  | Pop_apply parg -> Pop_apply (f parg)
  | op -> op

let map_ops pmap ops =
  List.map (path_op_map_path (Path.subst_map pmap)) ops

let rec filter_params map = function
  | [] -> []
  | (id, mty) :: tl ->
    if Ident.Map.mem id map then
      filter_params map tl
    else (id, mty) :: filter_params map tl (* TODO apply map on mty *)

let rec compute_map params (from : Path.t) (target : Path.t) =
  match from, target with
  | Pident from_id, Pident target_id when Ident.same from_id target_id ->
    Some Ident.Map.empty
  | Pident from_id, _ ->
    if List.exists (fun (id, _) -> Ident.same from_id id) params then
      Some (Ident.Map.singleton from_id target)
    else
      None
  | Pdot (from, s), Pdot (target, s2) ->
    if s = s2 then
      compute_map params from target
    else
      None
  | Pextra_ty (from, ety_f), Pextra_ty (target, ety_t) ->
    if ety_f = ety_t then
      compute_map params from target
    else
      None
  | Papply (from_fun, from_arg), Papply (target_fun, target_arg) ->
    Option.bind
      (compute_map params from_fun target_fun)
      (fun fun_instance ->
        match compute_map params from_arg target_arg with
        | None -> None
        | Some target_instance ->
          Some (Ident.Map.union (fun _ _ -> assert false) fun_instance target_instance)
      )
  | Pdot _, _ | Pextra_ty _, _ | Papply _, _ -> None

let compute_fresh_map params parg_from parg_target instances =
  match compute_map params parg_from parg_target with
  | None -> None
  | Some map ->
    let new_instance =
      List.map (fun (p, _) -> Ident.Map.find_opt p map) params
    in
    let eq_instances inst1 inst2 =
      List.for_all2 (Option.equal Path.same) inst1 inst2
    in
    if List.exists (eq_instances new_instance) instances then
      None
    else
      Some (map, new_instance)

let compute_all_new_instances static_apps path_pair =
  let maps, pp_instances =
    Path.Map.fold
      (fun parg id (maps, instances) ->
        match
          compute_fresh_map path_pair.pp_params
            (fst path_pair.pp_left) parg instances
        with
        | None -> (maps, instances)
        | Some (map, new_instance) ->
            ((id, map) :: maps, new_instance :: instances))
      static_apps ([], path_pair.pp_instances)
  in
  maps, { path_pair with pp_instances }

let instantiate_to_arg parg quantified_apps =
  List.fold_left_map
    (fun new_instances path_pair ->
      match
        compute_fresh_map path_pair.pp_params
          (fst path_pair.pp_left) parg path_pair.pp_instances
      with
      | None -> (new_instances, path_pair)
      | Some (map, new_inst) ->
        (
          (map, path_pair) :: new_instances,
          { path_pair with pp_instances = new_inst :: path_pair.pp_instances }
        )
      )
    [] quantified_apps

let rec build_path_target ?path data ops target_kind params =
  match ops with
  | [] ->
    let mi_desc =
      match target_kind with
      | Type n -> BaseType (n, [])
      | Module -> Mod
    in
    let mod_id, data = ModId.add { mi_path = path; mi_desc; } data
    in
    mod_id, mod_id, data, None
  | Pop_apply parg :: ops ->
    if Path.exists_free (List.map fst params) parg then
      let mod_id, data =
        ModId.add {
          mi_path = path;
          mi_desc = App { static_apps = Path.Map.empty; quantified_apps = [] };
        } data
      in
      mod_id, mod_id, data, Some (parg, ops)
    else
      let applied_id, id, data, final_arg =
      let path = Option.map (fun p -> Path.Papply (p, parg)) path in
        build_path_target ?path data ops target_kind params
      in
      let static_apps = Path.Map.singleton parg applied_id in
      let app_id, data =
        ModId.add {
          mi_path = path;
          mi_desc = App {static_apps; quantified_apps = []};
        } data
      in
      app_id, id, data, final_arg
  | Pop_dot s :: ops ->
    let proj_id, id, data, final_arg =
      let path = Option.map (fun p -> Path.Pdot (p, s)) path in
      build_path_target ?path data ops target_kind params
    in
    let projs = SMap.singleton s proj_id in
    let projs_id, data =
      ModId.add { mi_path = path; mi_desc = Projections projs; } data
    in
    projs_id, id, data, final_arg
  | Pop_extra_ty ety :: ops ->
    let proj_id, id, data, final_arg =
      let path = Option.map (fun p -> Path.Pextra_ty (p, ety)) path in
      build_path_target ?path data ops target_kind params
    in
    let projs = EtyMap.singleton ety proj_id in
    let projs_id, data =
      ModId.add { mi_path = path; mi_desc = ExtraProjs projs; } data
    in
    projs_id, id, data, final_arg

let rec get_path_target data mod_id ops target_kind params =
  let info = ModId.find mod_id data in
  (* assert (info.mi_path = None); *)
  match ops, info.mi_desc with
  | _, Alias id -> get_path_target data id ops target_kind params
  | [], _ -> mod_id, data, None, None
  | Pop_dot s :: ops, Projections projs ->
    begin match SMap.find s projs with
    | proj_id ->
      get_path_target data proj_id ops target_kind params
    | exception Not_found ->
      let path = Option.map (fun p -> Path.Pdot (p, s)) info.mi_path in
      let proj_id, id, data, final_arg =
        build_path_target ?path data ops target_kind params
      in
      let projs = SMap.add s proj_id projs in
      let data =
        ModId.update mod_id { info with mi_desc = Projections projs } data
      in
      id, data, final_arg, None
    end
  | Pop_apply parg :: ops, App { static_apps; quantified_apps } ->
    if Path.exists_free (List.map fst params) parg then
      mod_id, data, Some (parg, ops), None
    else begin
      match Path.Map.find parg static_apps with
      | ret_id ->
        get_path_target data ret_id ops target_kind params
      | exception Not_found ->
        let path = Option.map (fun p -> Path.Papply (p, parg)) info.mi_path in
        let ret_id, id, data, final_arg =
          build_path_target ?path data ops target_kind params
        in
        let new_instances, quantified_apps =
          instantiate_to_arg parg quantified_apps
        in
        let static_apps = Path.Map.add parg ret_id static_apps in
        let data =
          ModId.update mod_id
            { info with mi_desc = App {static_apps; quantified_apps } } data
        in
        id, data, final_arg, Some (ret_id, new_instances)
    end
  | Pop_extra_ty ety :: ops, ExtraProjs projs ->
    begin match EtyMap.find ety projs with
    | proj_id ->
      get_path_target data proj_id ops target_kind params
    | exception Not_found ->
      let path = Option.map (fun p -> Path.Pextra_ty (p, ety)) info.mi_path in
      let proj_id, id, data, final_arg =
        build_path_target ?path data ops target_kind params
      in
      let projs = EtyMap.add ety proj_id projs in
      let data =
        ModId.update mod_id { info with mi_desc = ExtraProjs projs } data
      in
      id, data, final_arg, None
    end
  | _ :: _, Mod ->
    let next_id, id, data, final_arg =
      build_path_target ?path:info.mi_path data ops target_kind params
    in
    let data =
      ModId.update mod_id { info with mi_desc = Alias next_id } data
    in
    id, data, final_arg, None
  | Pop_dot _ :: _, BaseType _ -> assert false
  | Pop_dot _ :: _, App _ -> assert false
  | Pop_dot _ :: _, ExtraProjs _ -> assert false
  | Pop_apply _ :: _, BaseType _ -> assert false
  | Pop_apply _ :: _, Projections _ -> assert false
  | Pop_apply _ :: _, ExtraProjs _ -> assert false
  | Pop_extra_ty _ :: _, BaseType _ -> assert false
  | Pop_extra_ty _ :: _, App _ -> assert false
  | Pop_extra_ty _ :: _, Projections _ -> assert false
  (* | _ :: _, _ -> assert false *)

let get_path_target_from_id eqs mod_id ops target_kind params =
  let target_id, data, final_arg, maybe_new_instances =
    get_path_target eqs.data mod_id ops target_kind params
  in
  target_id, { eqs with data }, final_arg, maybe_new_instances

let get_path_target eqs p target_kind params =
  let id, ops = decompose_path p in
  match Ident.Map.find id eqs.flex_heads with
  | mod_id ->
    get_path_target_from_id eqs mod_id ops target_kind params
  | exception Not_found ->
    let next_id, target_id, data, final_arg =
      build_path_target eqs.data ops target_kind params
    in
    let flex_heads = Ident.Map.add id next_id eqs.flex_heads in
    target_id, { data; flex_heads }, final_arg, None

let update_eqs id desc = function
  | HasContradiction -> HasContradiction
  | Constraints eqs ->
    Constraints { eqs with data = ModId.update id desc eqs.data }

let rec best_path_of_list = function
  | [] -> None
  | None :: tl -> best_path_of_list tl
  | Some p :: tl ->
    let path_score p =
      assert (Ident.rigid (Path.first p));
      if Path.rigid p then 3 else
      if Ident.rigid (Path.first p) then 2 else 1
    in
    let rec aux best_p score = function
      | [] -> Some best_p
      | None :: tl -> aux best_p score tl
      | Some p :: tl ->
        let score' = path_score p in
        if score' > score then
          aux p score' tl
        else
          aux best_p score tl
    in
    aux p (path_score p) tl

type new_eq =
  | PathEq of path_eq_kind * Path.t * Path.t
  | TypeEq of Types.type_expr * Types.type_expr

let rec update_path_name path acc eqs id =
  let info = ModId.find id eqs.data in
  match info.mi_path with
  | None ->
    let eqs = { eqs with
        data = ModId.update id {info with mi_path = Some path} eqs.data
    } in
    begin match info.mi_desc with
      | Alias id -> update_path_name path acc eqs id
      | Mod -> acc, eqs
      | BaseType (n, cstrs) ->
        assert (Ident.rigid (Path.first path));
        let eqs = { eqs with
          data = ModId.update id {mi_path = Some path; mi_desc = BaseType (n, [])} eqs.data
        } in
        let acc =
          List.fold_left
            (fun acc (tyl, ty) ->
              TypeEq (Btype.newgenty (Tconstr (path, tyl, ref Types.Mnil)), ty) :: acc) acc cstrs
        in
        acc, eqs
      | Projections projs ->
        SMap.fold
          (fun s id (acc, eqs) ->
            update_path_name (Path.Pdot (path, s)) acc eqs id)
          projs (acc, eqs)
      | ExtraProjs projs ->
        EtyMap.fold
          (fun ety id (acc, eqs) ->
            update_path_name (Path.Pextra_ty (path, ety)) acc eqs id)
          projs (acc, eqs)
      | App { static_apps } ->
        Path.Map.fold
          (fun parg id (acc, eqs) ->
            update_path_name (Path.Papply (path, parg)) acc eqs id)
          static_apps (acc, eqs)
    end
  | Some p ->
    begin match info.mi_desc with
      | Alias id -> update_path_name path acc eqs id
      | BaseType (n, []) ->
        PathEq (Type n, path, p) :: acc, eqs
      | BaseType (_, _ :: _) ->
        assert false (* Should not happen (I hope) *)
      | _ ->
        PathEq (Module, path, p) :: acc, eqs
    end

let update_path_name path acc eqs id =
  match eqs with
  | HasContradiction -> [], HasContradiction
  | Constraints eqs ->
    let acc, eqs = update_path_name path acc eqs id in
    acc, Constraints eqs

let rec add_all_path_eqs eq_kind ?prev acc = function
  | [] -> acc
  | None :: tl -> add_all_path_eqs eq_kind acc tl
  | Some p :: tl ->
    match prev with
    | None ->
      add_all_path_eqs eq_kind ~prev:p acc tl
    | Some p2 ->
      add_all_path_eqs eq_kind ~prev:p (PathEq (eq_kind, p, p2) :: acc) tl

let rec merge_ids ?path acc eqs id1 id2 =
  if id1 = id2 then id1, acc, eqs else
  match eqs with
  | HasContradiction -> id1, [], HasContradiction
  | Constraints { data } ->
  let info1 = ModId.find id1 data
  and info2 = ModId.find id2 data in
  let mi_path =
    best_path_of_list [path; info1.mi_path; info2.mi_path]
  in
  let id, acc, eqs =
    match info1.mi_desc, info2.mi_desc with
    | Alias id1, Alias id2 -> merge_ids ?path acc eqs id1 id2
    | Alias id1, _ -> merge_ids ?path acc eqs id1 id2
    | _, Alias id2 -> merge_ids ?path acc eqs id1 id2
    | Mod, _ ->
      id2, add_all_path_eqs Module acc [path; info1.mi_path; info2.mi_path], eqs
    | _, Mod ->
      id1, add_all_path_eqs Module acc [path; info1.mi_path; info2.mi_path], eqs
    (* | Equalities _, _ | _, Equalities _ -> assert false *)
    | App app1, App app2 ->
      let quantified_apps = app1.quantified_apps @ app2.quantified_apps in
      let eqs_ref = ref eqs and acc = ref acc in
      let static_apps =
        Path.Map.merge
          (fun parg i1 i2 ->
            merge_ids' (Option.map (fun p -> Path.Papply (p, parg)) mi_path) acc eqs_ref i1 i2)
          app1.static_apps app2.static_apps
      in
      let eqs =
        update_eqs id1
          { mi_path; mi_desc = App { static_apps; quantified_apps }; }
          !eqs_ref
      in
      (id1,
       add_all_path_eqs Module !acc [path; info1.mi_path; info2.mi_path],
       eqs)
    | Projections projs1, Projections projs2 ->
      let eqs_ref = ref eqs and acc = ref acc in
      let projs =
        SMap.merge
          (fun s i1 i2 -> merge_ids' (Option.map (fun p -> Path.Pdot (p, s)) mi_path) acc eqs_ref i1 i2)
          projs1 projs2
      in
      let eqs =
        update_eqs id1 { mi_path; mi_desc = Projections projs; } !eqs_ref
      in
      (id1,
       add_all_path_eqs Module !acc [path; info1.mi_path; info2.mi_path],
       eqs)
    | ExtraProjs projs1, ExtraProjs projs2 ->
      let eqs_ref = ref eqs and acc = ref acc in
      let projs =
        EtyMap.merge
          (fun ety i1 i2 ->
            merge_ids' (Option.map (fun p -> Path.Pextra_ty (p, ety)) mi_path) acc eqs_ref i1 i2)
          projs1 projs2
      in
      let eqs =
        update_eqs id1 { mi_path; mi_desc = ExtraProjs projs; } !eqs_ref
      in
      (id1,
       add_all_path_eqs Module !acc [path; info1.mi_path; info2.mi_path],
       eqs)
    | BaseType (n1, l1), BaseType (n2, l2) ->
      assert (n1 = n2);
      let acc, eqs =
        match mi_path with
        | None ->
          let eqs =
            update_eqs id1 { mi_path; mi_desc = BaseType (n1, l1 @ l2); } eqs
          in
          acc, eqs
        | Some path ->
          assert (Ident.rigid (Path.first path));
          let eqs =
            update_eqs id1 { mi_path; mi_desc = BaseType (n1, []); } eqs
          in
          let acc =
            List.fold_left
              (fun acc (tyl, ty) ->
                TypeEq (Btype.newgenty (Tconstr (path, tyl, ref Types.Mnil)), ty) :: acc) acc (l1 @ l2)
          in
          acc, eqs
      in
      (id1,
       add_all_path_eqs (Type n1) acc [path; info1.mi_path; info2.mi_path],
       eqs)
    | BaseType _, (App _ | Projections _ | ExtraProjs _)
    | App _, (BaseType _ | Projections _ | ExtraProjs _)
    | Projections _, (BaseType _ | App _ | ExtraProjs _)
    | ExtraProjs _, (BaseType _ | App _ | Projections _) ->
      id1, [], HasContradiction
  in
  let eqs =
    if id1 = id then eqs else
      update_eqs id1 { mi_path; mi_desc = Alias id; } eqs
  in
  let eqs =
    if id2 = id then eqs else
      update_eqs id2 { mi_path; mi_desc = Alias id; } eqs
  in
  id, acc, eqs
and merge_ids' path acc eqs id1 id2 =
  match id1, id2 with
  | Some id1, Some id2 ->
    let id, acc', eqs' = merge_ids !acc !eqs id1 id2 in
    let acc', eqs' =
      match path with
      | Some path -> update_path_name path acc' eqs' id
      | None -> acc', eqs'
    in
    eqs := eqs';
    acc := acc';
    Some id
  | Some id, None | None, Some id ->
    begin
      match path with
      | Some path ->
        let acc', eqs' = update_path_name path !acc !eqs id in
        eqs := eqs';
        acc := acc';
        Some id
      | None -> Some id
    end
  | None, None -> assert false (* Should not happen *)

let normalize_path env kind p =
  match kind with
  | Module -> Env.normalize_module_path (Some Location.none) env p
  | Type _n -> normalize_type_path env p

let rec merge_path_ids env eqs id1 id2 =
  let _, acc, eqs = merge_ids [] eqs id1 id2 in
  List.fold_left
    (fun eqs -> function
      | TypeEq (ty1, ty2) -> add_type_type_eq env ~env_params:env [] ty1 ty2 eqs
      | PathEq (k, p1, p2) -> merge_paths env ~env_params:env [] k p1 p2 eqs)
    eqs acc
and merge_paths env ?env_params params eq_kind p1 p2 eqs =
  let env_params =
    match env_params with
    | Some env_params -> env_params
    | None ->
      List.fold_left
        (fun env (id, mty) -> Env.add_module id Mp_present IILocal mty env)
        env params
  in
  match eqs with
  | HasContradiction -> HasContradiction
  | Constraints eqs ->
    merge_paths_normalized env ~env_params params eq_kind
      (normalize_path env_params eq_kind p1)
      (normalize_path env_params eq_kind p2)
      eqs
and merge_paths_normalized env ~env_params params eq_kind p1 p2 eqs =
  match Ident.rigid (Path.first p1), Ident.rigid (Path.first p2) with
  | true, true ->
    begin match Path.merge p1 p2 with
      | Some sub_eqs ->
        List.fold_left
          (fun eqs (p1, p2) ->
            merge_paths env ~env_params params Module p1 p2 eqs)
          (Constraints eqs) sub_eqs
      | None ->
        if eq_kind = Module then HasContradiction else
          match
            Env.find_type_expansion p1 env_params,
            Env.find_type_expansion p2 env_params
          with
          | (([], ty1, _), ([], ty2, _)) ->
            let () = assert false in
            add_type_type_eq env ~env_params:env_params params ty1 ty2 (Constraints eqs)
          | _ -> assert false (* TODO *)
          | exception Not_found -> HasContradiction
    end
  | false, false ->
    begin
      let id1, eqs, final_arg1, new_instances1 =
        get_path_target eqs p1 eq_kind params
      in
      let id2, eqs, final_arg2, new_instances2 =
        get_path_target eqs p2 eq_kind params
      in
      let eqs = apply_new_instances env new_instances1 (Constraints eqs) in
      let eqs = apply_new_instances env new_instances2 eqs in
      match final_arg1, final_arg2 with
      | None, None -> merge_path_ids env eqs id1 id2
      | _, _ ->
        let eqs =
          match final_arg1 with
          | None -> eqs
          | Some (parg1, ops1) ->
            add_quantified_app env eq_kind params id1 parg1 ops1
              (CE_PathF (id2, final_arg2)) eqs
        in
        let eqs =
          match final_arg2 with
          | None -> eqs
          | Some (parg2, ops2) ->
            add_quantified_app env eq_kind params id2 parg2 ops2
              (CE_PathF (id1, final_arg1)) eqs
        in
        eqs
    end
  | true, false ->
    let id2, eqs, final_arg2, new_instances2 =
      get_path_target eqs p2 eq_kind params
    in
    let eqs = apply_new_instances env new_instances2 (Constraints eqs) in
    merge_path_with_rigid env params eq_kind id2 final_arg2 p1 eqs
  | false, true ->
    let id1, eqs, final_arg1, new_instances1 =
      get_path_target eqs p1 eq_kind params
    in
    let eqs = apply_new_instances env new_instances1 (Constraints eqs) in
    merge_path_with_rigid env params eq_kind id1 final_arg1 p2 eqs
and merge_path_with_rigid env params eq_kind id1 final_arg1 p2 eqs =
  match final_arg1 with
  | None ->
    let acc, eqs = update_path_name p2 [] eqs id1 in
    List.fold_left
      (fun eqs -> function
        | TypeEq (ty1, ty2) -> add_type_type_eq env ~env_params:env [] ty1 ty2 eqs
        | PathEq (k, p1, p2) -> merge_paths env ~env_params:env [] k p1 p2 eqs)
      eqs acc
  | Some (parg, ops) ->
    add_quantified_app env eq_kind params id1 parg ops (CE_PathR p2) eqs
and add_quantified_app env eq_kind params id parg ops pp_right eqs =
  match eqs with HasContradiction -> HasContradiction
  | Constraints eqs ->
  let info = ModId.find id eqs.data in
  assert (info.mi_path = None); (* TODO : Should this change behaviour ? *)
  let ce = {
      eq_kind;
      pp_params = params;
      pp_instances = [];
      pp_left = (parg, ops);
      pp_right;
    }
  in
  let static_apps, quantified_apps = match info.mi_desc with
    | App { static_apps; quantified_apps } ->
      static_apps, quantified_apps
    | Mod | Alias _ -> assert false (* Should not happen ? *)
    | _ -> assert false (* Cannot happen *)
  in
  let maps, ce = compute_all_new_instances static_apps ce in
  let mi_desc =
    App {
        static_apps;
        quantified_apps = ce :: quantified_apps;
      }
  in
  List.fold_left
    (fun eqs (id, map) ->
      add_path_pair_instance env id ce eqs map)
    (Constraints { eqs with
      data = ModId.update id {info with mi_desc} eqs.data
    })
    maps
and add_path_pair_instance env next_id path_pair eqs map =
  let ops = map_ops map (snd path_pair.pp_left)
  and params = filter_params map path_pair.pp_params
  in
  match eqs with HasContradiction -> HasContradiction
  | Constraints eqs ->
    match path_pair.pp_right with
    | CE_PathR p ->
      let id, eqs, final_arg, new_instances =
        get_path_target_from_id eqs next_id ops path_pair.eq_kind params
      in
      let eqs = apply_new_instances env new_instances (Constraints eqs) in
      merge_path_with_rigid env params path_pair.eq_kind
        id final_arg (Path.subst_map map p) eqs
    | CE_PathF (id_r, None) ->
      begin
        let id, eqs, final_arg, new_instances =
          get_path_target_from_id eqs next_id ops path_pair.eq_kind params
        in
        let eqs = apply_new_instances env new_instances (Constraints eqs) in
        match final_arg with
        | None -> merge_path_ids env eqs id id_r
        | Some (parg, ops) ->
          add_quantified_app env path_pair.eq_kind params id parg ops
            (CE_PathF (id_r, None)) eqs
      end
    | CE_PathF (id_r, Some (parg_r, ops_r)) ->
      begin
        let ops_r = map_ops map (Pop_apply parg_r :: ops_r) in
        let id1, eqs, final_arg1, new_instances1 =
          get_path_target_from_id eqs next_id ops path_pair.eq_kind params
        in
        let id2, eqs, final_arg2, new_instances2 =
          get_path_target_from_id eqs id_r ops_r path_pair.eq_kind params
        in
        let eqs = apply_new_instances env new_instances1 (Constraints eqs) in
        let eqs = apply_new_instances env new_instances2 eqs in
        match final_arg1, final_arg2 with
        | None, None -> merge_path_ids env eqs id1 id2
        | _, _ ->
          let eqs =
            match final_arg1 with
            | None -> eqs
            | Some (parg1, ops1) ->
              add_quantified_app env path_pair.eq_kind params id1 parg1 ops1
                (CE_PathF (id2, final_arg2)) eqs
          in
          let eqs =
            match final_arg2 with
            | None -> eqs
            | Some (parg2, ops2) ->
              add_quantified_app env path_pair.eq_kind params id2 parg2 ops2
                (CE_PathF (id1, final_arg1)) eqs
          in
          eqs
      end
    | CE_Type _ -> assert false (* TODO *)
and apply_new_instances env new_instances eqs =
  match new_instances with
  | None -> eqs
  | Some (id, map_path_pair_list) ->
    List.fold_left
      (fun eqs (map, path_pair) ->
        add_path_pair_instance env id path_pair eqs map)
      eqs map_path_pair_list
and add_path_type_eq env ?env_params params p1 tyl1 ty2 eqs =
  let env_params =
    match env_params with
    | Some env_params -> env_params
    | None ->
      List.fold_left
        (fun env (id, mty) -> Env.add_module id Mp_present IILocal mty env)
        env params
  in
  match eqs with
  | HasContradiction -> HasContradiction
  | Constraints eqs ->
    match Types.get_desc ty2 with
    | Tconstr (p2, [], _) when tyl1 = [] ->
      merge_paths env ~env_params params (Type 0) p1 p2 (Constraints eqs)
    | _ ->
      let p1 =
        Env.normalize_type_path (Some Location.none) env_params (path_subst_map env eqs p1)
      in
      if Ident.rigid (Path.first p1) then
        add_type_type_eq env ~env_params params
          (Btype.newgenty (Tconstr (p1, tyl1, ref Types.Mnil))) ty2
          (Constraints eqs)
      else
        let id, eqs, final_arg, new_instances =
          get_path_target eqs p1 (Type (List.length tyl1)) params
        in
        match apply_new_instances env new_instances (Constraints eqs) with
        | HasContradiction -> HasContradiction
        | Constraints eqs ->
          match final_arg with
          | Some (parg, ops) ->
            add_quantified_app
                env (Type (List.length tyl1)) params id parg ops
                (CE_Type (tyl1, ty2)) (Constraints eqs)
          | None ->
            let info = ModId.find id eqs.data in
            match info.mi_desc with
            | BaseType (n, cstrs) ->
              assert (info.mi_path = None); (* TODO *)
              Constraints { eqs with
                data =
                  ModId.update id
                    {info with mi_desc = BaseType (n, (tyl1, ty2) :: cstrs) }
                    eqs.data
              }
            | _ -> assert false (* Should not happen *)
and add_type_type_eq env ~env_params params ty1 ty2 eqs =
  match Types.get_desc ty1, Types.get_desc ty2 with
  | (Tvar _, _) | (_, Tvar _) -> eqs
  | (Tconstr (p1, [], _), Tconstr (p2, [], _))
    when Env.Unscoped.path_equiv env_params p1 p2 [@alert "-dangerous"] -> eqs
  | _, _ ->
    let ty1' = !expand_head_rigid env_params ty1 in
    let ty2' = !expand_head_rigid env_params ty2 in
    match Types.get_desc ty1', Types.get_desc ty2' with
    | Tvar _, _ | _, Tvar _ -> eqs
    | Tconstr (p1, tyl1, _), Tconstr (p2, tyl2, _) ->
      if Ident.rigid (Path.first p1) then
        if Ident.rigid (Path.first p2) then
          match merge_paths env ~env_params params (Type (List.length tyl1)) p1 p2 eqs with
          | HasContradiction -> HasContradiction
          | eqs ->
            let () = assert (List.length tyl1 = List.length tyl2) in
            List.fold_left2
              (fun eqs t1 t2 -> add_type_type_eq env ~env_params params t1 t2 eqs)
              eqs tyl1 tyl2
        else
          add_path_type_eq env ~env_params params p2 tyl2 ty1 eqs
      else
        add_path_type_eq env ~env_params params p1 tyl1 ty2 eqs
    | Tconstr (p, tyl, _), _ when not (Ident.rigid (Path.first p)) ->
      add_path_type_eq env ~env_params params p tyl ty2 eqs
    | _, Tconstr (p, tyl, _) when not (Ident.rigid (Path.first p)) ->
      add_path_type_eq env ~env_params params p tyl ty1 eqs
    | Tarrow (l1, t1, u1, _), Tarrow (l2, t2, u2, _) ->
      if Btype.compatible_labels ~in_pattern_mode:false l1 l2 then
        eqs
        |> add_type_type_eq env ~env_params params t1 t2
        |> add_type_type_eq env ~env_params params u1 u2
      else HasContradiction
    | Ttuple tl1, Ttuple tl2 ->
      if List.length tl1 = List.length tl2 then
        List.fold_left2
          (fun eqs (label1, t1) (label2, t2) ->
            if Option.equal String.equal label1 label2 then
              add_type_type_eq env ~env_params params t1 t2 eqs
            else HasContradiction)
          eqs tl1 tl2
      else HasContradiction
    | Tnil, Tnil -> eqs
    | Tpoly (t1, []), Tpoly (t2, []) ->
      add_type_type_eq env ~env_params params t1 t2 eqs
    | Tpackage _, Tpackage _ | Tvariant _, Tvariant _
    | Tobject _, Tobject _ | Tfield _, Tfield _
    | Tpoly _, Tpoly _ | Tunivar _, Tunivar _
    | Tfunctor _, Tfunctor _ | Tfunctor _, Tarrow _ | Tarrow _, Tfunctor _ ->
      Format.eprintf "ForgotAdd : %a %a = %a\n"
        (Format.pp_print_list Ident.print) (List.map Pair.fst params)
        Rawprinttyp.type_expr ty1
        Rawprinttyp.type_expr ty2;
      eqs
    | Tlink _, _ | _, Tlink _ | Texpand _, _ | _, Texpand _
    | Tsubst _, _ | _, Tsubst _ -> assert false
    | Tarrow _, _ | _, Tarrow _ | Tfunctor _, _ | _, Tfunctor _
    | Tpackage _, _ | _, Tpackage _ | Ttuple _, _ | _, Ttuple _
    | Tnil, _ | _, Tnil | Tfield _, _ | _, Tfield _ | Tpoly _, _ | _, Tpoly _
    | Tobject _, _ | _, Tobject _ | Tvariant _, _ | _, Tvariant _
    | Tunivar _, _ | _, Tunivar _ ->
      HasContradiction

let is_empty eqs =
  Ident.Map.is_empty eqs.flex_heads

(* let solve_opt env k i p = function
  | HasContradiction -> HasContradiction
  | Constraints eqs -> solve env ~env_params:env k [] i p eqs *)

let merge env eqs1 eqs2 =
  let data =
    ModId.union (fun _ _ _ -> assert false (* Should be disjoint *))
      eqs1.data
      eqs2.data
  in
  let pairs = ref [] in
  let flex_heads =
    Ident.Map.union (fun _ i1 i2 -> pairs := (i1, i2) :: !pairs; Some i1)
      eqs1.flex_heads
      eqs2.flex_heads
  in
  List.fold_left
    (fun eqs (i1, i2) -> merge_path_ids env eqs i1 i2)
    (Constraints { data; flex_heads })
    !pairs

let merge env eqs1 eqs2 =
  (* Format.eprintf "Merge : %a%a\n"
    (Format_doc.compat print) eqs1
    (Format_doc.compat print) eqs2; *)
  match eqs1, eqs2 with
  | HasContradiction, _ | _, HasContradiction -> HasContradiction
  | Constraints eqs1, Constraints eqs2 ->
    if is_empty eqs1 then Constraints eqs2 else begin
      if is_empty eqs2 then Constraints eqs1 else begin
        merge env eqs1 eqs2
      end
    end

(* let merge env eqs1 eqs2 =
  let res = merge env eqs1 eqs2 in
  if not (is_empty eqs1) && not (is_empty eqs2) then
    Format.eprintf "Merge : %a\n%a\n ==> %a\n"
      (Format_doc.compat print) eqs1
      (Format_doc.compat print) eqs2
      (Format_doc.compat print) res;
  res *)

type compatibility =
  | Same
  | Compatible
  | Incompatible

let combine_compatibility c1 c2 =
  match c1, c2 with
  | Incompatible, _ | _, Incompatible -> Incompatible
  | Same, Same -> Same
  | Same, Compatible | Compatible, Same
  | Compatible, Compatible -> Compatible

let rec compatibility env ty1 ty2 =
  match Types.get_desc ty1, Types.get_desc ty2 with
  | (Tvar _, _) | (_, Tvar _) -> Compatible
  | (Tconstr (p1, [], _), Tconstr (p2, [], _))
    when Env.Unscoped.path_equiv env p1 p2 [@alert "-dangerous"] ->
      Same
  | _ ->
    let ty1' = !expand_head_rigid env ty1 in
    let ty2' = !expand_head_rigid env ty2 in
    match Types.get_desc ty1', Types.get_desc ty2' with
    | Tvar _, _ | _, Tvar _ -> Compatible
    | Tconstr (p1, tyl1, _), Tconstr (p2, tyl2, _)
        when Path.rigid p1 && Path.rigid p2
            && Env.Unscoped.path_equiv env p1 p2 [@alert "-dangerous"] ->
      compatibility_list env tyl1 tyl2
    | Tconstr (p, _, _), _ | _, Tconstr (p, _, _) ->
      if Ident.rigid (Path.first p) then Incompatible else Compatible
    | Tarrow (l1, t1, u1, _), Tarrow (l2, t2, u2, _) ->
      if Btype.compatible_labels ~in_pattern_mode:false l1 l2 then
        combine_compatibility (compatibility env t1 t2) (compatibility env u1 u2)
      else
        Incompatible
    | Tfunctor (l1, _, _, _), Tfunctor (l2, _, _, _)
    | Tfunctor (l1, _, _, _), Tarrow (l2, _, _, _)
    | Tarrow (l1, _, _, _), Tfunctor (l2, _, _, _) ->
      if Btype.compatible_labels ~in_pattern_mode:false l1 l2 then
        Compatible
      else Incompatible
    | Ttuple tl1, Ttuple tl2 ->
      if List.length tl1 <> List.length tl2 then
        Incompatible
      else
        compatibility_labeled_list env tl1 tl2
    | Tnil, Tnil -> Same
    | Tpoly (t1, _), Tpoly (t2, _) -> compatibility env t1 t2
    | Tunivar _, Tunivar _ -> Compatible
    | Tpackage _, Tpackage _ | Tvariant _, Tvariant _
    | Tobject _, Tobject _ | Tfield _, Tfield _ -> Compatible
    | Tlink _, _ | _, Tlink _ | Texpand _, _ | _, Texpand _
    | Tsubst _, _ | _, Tsubst _ -> assert false
    | Tarrow _, _ | _, Tarrow _ | Tfunctor _, _ | _, Tfunctor _
    | Tpackage _, _ | _, Tpackage _ | Ttuple _, _ | _, Ttuple _
    | Tnil, _ | _, Tnil | Tfield _, _ | _, Tfield _ | Tpoly _, _ | _, Tpoly _
    | Tobject _, _ | _, Tobject _ | Tvariant _, _ | _, Tvariant _ ->
      Incompatible
and compatibility_list env tyl1 tyl2 =
  List.fold_left2
    (fun c ty1 ty2 -> combine_compatibility c (compatibility env ty1 ty2))
    Same tyl1 tyl2
and compatibility_labeled_list env tyl1 tyl2 =
  List.fold_left2
    (fun c (label1, ty1) (label2, ty2) ->
      if label1 <> label2 then Incompatible else
        combine_compatibility c (compatibility env ty1 ty2))
    Same tyl1 tyl2

let has_error_type_constraints env eqs =
  let base_type_abs path = function
    | BaseType (_, cstrs) ->
      let rec aux = function
        | [] -> false
        | (tyl, ty) :: tl ->
          begin match path with
            | Some path -> compatibility env (Btype.newgenty (Tconstr (path, tyl, ref Types.Mnil))) ty = Incompatible
            | None -> false
          end
          || List.exists (fun (tyl2, ty2) ->
            compatibility_list env tyl tyl2 = Same && compatibility env ty ty2 = Incompatible) tl
          || aux tl
      in aux cstrs
    | _ -> false
  in
  ModId.exists (fun _ info -> base_type_abs info.mi_path info.mi_desc) eqs.data

let has_error env = function
  | HasContradiction -> true
  | Constraints eqs ->
    has_error_type_constraints env eqs

(* let same_freeness id {pp_params; pp_rigid; pp_flex} =
  List.exists (fun (id', _) -> Ident.same id id') pp_params
  || Path.exists_free [id] pp_rigid.path = Path.exists_free [id] pp_flex.path *)

(* let generalize _env param eqs =
  match param, eqs with
  | Types.Unit, _ | Types.Named (_, None, _), _ | _, HasContradiction -> eqs
  | Types.Named (_, Some _id, _mty), Constraints eqs ->
    assert (is_empty (Constraints eqs));
    Constraints eqs *)
    (* if Ident.Map.exists (fun _ p -> Path.exists_free [id] p) eqs.solved_flex
      || Ident.Map.exists
              (fun _ pl -> List.exists (fun ps -> not (same_freeness id ps)) pl)
              eqs.flex_rigid_heads
    then begin
      Format.eprintf "No sol when generalizing %a\n" Ident.print id;
      HasContradiction
    end else begin
      let type_constraints =
        Ident.Map.map
          (List.map
            (function
              | PathEqType eq ->
                PathEqType { eq with params = (id, mty) :: eq.params }
              | PathEqPath eq ->
                PathEqPath { eq with params = (id, mty) :: eq.params }))
          eqs.type_constraints
      in
      let flex_rigid_heads =
        Ident.Map.map
          (List.map (fun ps -> {ps with pp_params = (id, mty) :: ps.pp_params}))
          eqs.flex_rigid_heads
      in
      let flex_flex =
        List.map
          (fun (k, params, p1, p2) -> (k, (id, mty) :: params, p1, p2))
          eqs.flex_flex
      in
      Constraints {
        solved_flex = eqs.solved_flex;
        type_constraints;
        flex_rigid_heads;
        flex_flex;
      }
    end *)



let add_path_eq env eq_kind p1 p2 eqs =
  (* Format.eprintf "Add %a = %a to\n%a\n"
    (Format_doc.compat Path.print) p1
    (Format_doc.compat Path.print) p2
    (Format_doc.compat print) eqs; *)
  merge_paths env [] eq_kind p1 p2 eqs
let add_path_type_eq env params p tyl ty eqs =
  match tyl, Types.get_desc ty with
  | [], Tconstr (p2, [], _) -> merge_paths env params (Type 0) p p2 eqs
  | _ -> add_path_type_eq env params p tyl ty eqs

let add_type_eq env t1 t2 eqs =
  add_type_type_eq env ~env_params:env [] t1 t2 eqs

type tmp = (params * Path.t * Types.type_expr list * Types.type_expr) list

let empty_tmp = []
let merge_tmp l1 l2 = l1 @ l2

let generalize _env param l =
  match param with
  | Types.Unit | Types.Named (_, None, _) -> l
  | Types.Named (_, Some id, mty) ->
    List.map (fun (params, p, tyl, ty) -> ((id, mty) :: params, p, tyl, ty)) l

let of_tmp env l =
  List.fold_left
    (fun eqs (params, p, tyl, ty) ->
      match Types.get_desc ty with
      | Tconstr (p2, [], _) when tyl = [] ->
        let rec filter_params = function
          | [] -> []
          | (id, _) as hd :: tl ->
            match filter_params tl with
            | [] ->
              if Path.exists_free [id] p || Path.exists_free [id] p2
              then
                [hd]
              else
                []
            | tl -> hd :: tl
        in
        add_path_type_eq env (filter_params params) p tyl ty eqs
      | _ ->
        (* if (params <> []) then
          Format.eprintf "%a %a(%a) => %a\n"
            (Format_doc.compat Pp.print_params) params
            (Format_doc.compat Path.print) p
            (Format.pp_print_list Rawprinttyp.type_expr) tyl
            Rawprinttyp.type_expr ty;
        assert (params = []); *)
        add_path_type_eq env params p tyl ty eqs
    )
    empty
    l

let is_empty l = l = []

let add_path_type_eq _env p tyl ty l = ([], p, tyl, ty) :: l
