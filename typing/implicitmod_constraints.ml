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

type path_eq_kind =
  | Module
  | Type

type path_with_head = {
  path : Path.t;
  (* first : Ident.t; *)
}

type params = (Ident.t * Types.module_type) list

[@@@warning "-37-69"]

type path_pair = {
  eq_kind : path_eq_kind;
  pp_params : params;
  pp_rigid : path_with_head;
  pp_flex : path_with_head;
}

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

type type_constraint =
  | PathEqType of {
    params : params;
    path_flex : path_with_head;
    tyl : Types.type_expr list;
    ty2 : Types.type_expr;
  }
  | PathEqPath of {
    params : params;
    path_flex1 : path_with_head;
    tyl1 : Types.type_expr list;
    path_flex2 : path_with_head;
    tyl2 : Types.type_expr list;
  }

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

type module_desc =
  | Alias of ModId.t
  | BaseType of (Types.type_expr list * Types.type_expr) list
  | Mod
  (* | Equalities of path_pair list *)
  | App of {
      static_apps : ModId.t Path.Map.t;
      quantified_apps : path_pair list;
    }
  | Projections of ModId.t SMap.t
  | ExtraProjs of ModId.t EtyMap.t

type module_info = {
  mi_path : Path.t; (*equiv_path option;*)
  mi_desc : module_desc;
}

type t_inner = {
  flex_heads : ModId.t Ident.Map.t;
  data : module_info ModId.map;
  type_constraints : type_constraint list Ident.Map.t;
}

type t =
  | HasContradiction
  | Constraints of t_inner

let empty = Constraints {
  flex_heads = Ident.Map.empty;
  data = ModId.empty_map;
  type_constraints = Ident.Map.empty;
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

  let print_mi_desc fmt = function
    | Mod ->
      Format_doc.fprintf fmt "Mod"
    | BaseType [([], ty)] ->
      Format_doc.fprintf fmt "=t %a" !type_expr_printer ty
    | BaseType cstrs ->
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
    | App _ ->
      Format_doc.fprintf fmt "@[App constraints@]"

  let pp_info fmt info =
    Format_doc.fprintf fmt "@[{p = %a;@ d = %a}@]"
      (* (Format_doc.pp_print_option Path.print) info.mi_path *)
      Path.print info.mi_path
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

  let print_one_type_eq fmt = function
  | PathEqType { params; path_flex; tyl; ty2 } ->
      Format_doc.fprintf fmt "%a %a(%a) => %a\n"
        print_params params
        Path.print path_flex.path
        (Format_doc.pp_print_list !type_expr_printer) tyl
        !type_expr_printer ty2
  | PathEqPath { params; path_flex1; tyl1; path_flex2; tyl2 } ->
      Format_doc.fprintf fmt "%a %a(%a) => %a(%a)\n"
        print_params params
        Path.print path_flex1.path
        (Format_doc.pp_print_list !type_expr_printer) tyl1
        Path.print path_flex2.path
        (Format_doc.pp_print_list !type_expr_printer) tyl2

  let pp_type_constraints fmt type_constraints =
    let aux fmt () =
      Ident.Map.iter
        (fun i constraints ->
          Format_doc.fprintf fmt "\t%s[%d] =>\n\t@[<hov>%a@]"
            (Ident.name i)
            (List.length constraints)
            (Format_doc.pp_print_list print_one_type_eq) constraints)
        type_constraints
    in
    Format_doc.fprintf fmt "@[<hov>type_constraints = %a@]" aux ()

  let print_inner fmt eqs =
    Format_doc.fprintf fmt "@[<hov2>{%a;@ %a;@ %a}@]"
      pp_flex_heads eqs.flex_heads
      pp_data eqs.data
      pp_type_constraints eqs.type_constraints
end

let print fmt eqs =
  match eqs with
  | Constraints eqs -> Pp.print_inner fmt eqs
  | HasContradiction -> Format_doc.fprintf fmt "Absurd"

let print fmt eqs =
  if true then Format_doc.fprintf fmt "%a\n" print eqs else ()

let rec add_ops_to_path p = function
  | [] -> p
  | Pop_dot s :: ops -> add_ops_to_path (Path.Pdot (p, s)) ops
  | Pop_apply parg :: ops -> add_ops_to_path (Path.Papply (p, parg)) ops
  | Pop_extra_ty ety :: ops -> add_ops_to_path (Path.Pextra_ty (p, ety)) ops

let rec build_normalized_path env eqs ops id =
  let info = ModId.find id eqs.data in
  match info.mi_desc, ops with
  | _, [] -> info.mi_path
  | Alias id, _ -> build_normalized_path env eqs ops id
  | BaseType _, _ :: _ -> assert false
  | (Mod (*| Equalities _*)), _ -> add_ops_to_path info.mi_path ops
  | Projections projs, Pop_dot s :: ops ->
    begin match SMap.find s projs with
    | id' -> build_normalized_path env eqs ops id'
    | exception Not_found ->
      add_ops_to_path info.mi_path ops
    end
  | ExtraProjs projs, Pop_extra_ty ety :: ops ->
    begin match EtyMap.find ety projs with
    | id' -> build_normalized_path env eqs ops id'
    | exception Not_found ->
      add_ops_to_path info.mi_path ops
    end
  | App { static_apps }, Pop_apply parg :: ops ->
    let parg = normalize_module_path env eqs parg in
    begin match Path.Map.find parg static_apps with
    | constraints -> build_normalized_path env eqs ops constraints
    | exception Not_found ->
      add_ops_to_path info.mi_path ops
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
      build_normalized_path env eqs ops constraints
    | exception Not_found -> p

let rec normalize_type_path env eqs p =
  let p' = path_subst_map env eqs p in
  match Env.find_type_expansion p' env with
  | (params, ty, _) ->
    begin
      assert (params = []);
      match Types.get_desc ty with
      | Tconstr (p', [], _) ->
        normalize_type_path env eqs p'
      | _ ->
        Env.normalize_type_path (Some Location.none) env p', Some ty
    end
  | exception Not_found ->
    Env.normalize_type_path (Some Location.none) env p', None

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

let rec build_path_target prefix data ops target_kind params =
  match ops with
  | [] ->
    let mi_desc =
      match target_kind with
      | Type -> BaseType []
      | Module -> Mod
    in
    let mod_id, data = ModId.add { mi_path = prefix; mi_desc; } data
    in
    mod_id, mod_id, data, None
  | Pop_apply parg :: ops ->
    if Path.exists_free (List.map fst params) parg then
      let mod_id, data =
        ModId.add {
          mi_path = prefix;
          mi_desc = App { static_apps = Path.Map.empty; quantified_apps = [] };
        } data
      in
      mod_id, mod_id, data, Some parg
    else
      let applied_id, id, data, final_arg =
        build_path_target (Path.Papply (prefix, parg)) data
          ops target_kind params
      in
      let static_apps = Path.Map.singleton parg applied_id in
      let app_id, data =
        ModId.add {
          mi_path = prefix;
          mi_desc = App {static_apps; quantified_apps = []};
        } data
      in
      app_id, id, data, final_arg
  | Pop_dot s :: ops ->
    let proj_id, id, data, final_arg =
      build_path_target (Path.Pdot (prefix, s)) data ops target_kind params
    in
    let projs = SMap.singleton s proj_id in
    let projs_id, data =
      ModId.add { mi_path = prefix; mi_desc = Projections projs; } data
    in
    projs_id, id, data, final_arg
  | Pop_extra_ty ety :: ops ->
    let proj_id, id, data, final_arg =
      build_path_target (Path.Pextra_ty (prefix, ety)) data
        ops target_kind params
    in
    let projs = EtyMap.singleton ety proj_id in
    let projs_id, data =
      ModId.add { mi_path = prefix; mi_desc = ExtraProjs projs; } data
    in
    projs_id, id, data, final_arg

let rec get_path_target data mod_id ops target_kind params =
  let info = ModId.find mod_id data in
  (* assert (info.mi_path = None); *)
  match ops, info.mi_desc with
  | _, Alias id -> get_path_target data id ops target_kind params
  | [], _ -> mod_id, data, None
  | Pop_dot s :: ops, Projections projs ->
    begin match SMap.find s projs with
    | proj_id ->
      get_path_target data proj_id ops target_kind params
    | exception Not_found ->
      let proj_id, id, data, final_arg =
        build_path_target info.mi_path data ops target_kind params
      in
      let projs = SMap.add s proj_id projs in
      let data =
        ModId.update mod_id { info with mi_desc = Projections projs } data
      in
      id, data, final_arg
    end
  | Pop_apply parg :: ops, App { static_apps; _ } ->
    if Path.exists_free (List.map fst params) parg then
      mod_id, data, Some parg
    else begin
      match Path.Map.find parg static_apps with
      | ret_id ->
        get_path_target data ret_id ops target_kind params
      | exception Not_found ->
        assert false (* TODO *)
    end
  | Pop_extra_ty ety :: ops, ExtraProjs projs ->
    begin match EtyMap.find ety projs with
    | proj_id ->
      get_path_target data proj_id ops target_kind params
    | exception Not_found ->
      let proj_id, id, data, final_arg =
        build_path_target info.mi_path data ops target_kind params
      in
      let projs = EtyMap.add ety proj_id projs in
      let data =
        ModId.update mod_id { info with mi_desc = ExtraProjs projs } data
      in
      id, data, final_arg
    end
  (* | _ :: _, Equalities _ ->
    assert false (* TODO *) *)
  | _ :: _, Mod ->
    assert (not (Ident.rigid (Path.first info.mi_path)));
    let next_id, id, data, final_arg =
      build_path_target info.mi_path data ops target_kind params
    in
    let data =
      ModId.update mod_id { info with mi_desc = Alias next_id } data
    in
    id, data, final_arg
  | _ :: _, _ -> assert false

let get_path_target eqs id ops target_kind params =
  match Ident.Map.find id eqs.flex_heads with
  | mod_id ->
    let target_id, data, final_arg =
      get_path_target eqs.data mod_id ops target_kind params
    in
    target_id, { eqs with data }, final_arg
  | exception Not_found ->
    let next_id, target_id, data, final_arg =
      build_path_target (Path.Pident id) eqs.data ops target_kind params
    in
    let flex_heads = Ident.Map.add id next_id eqs.flex_heads in
    target_id, { eqs with data; flex_heads }, final_arg

let get_path_target eqs p target_kind params =
  let id, ops = decompose_path p in
  get_path_target eqs id ops target_kind params

let update_eqs id desc = function
  | HasContradiction -> HasContradiction
  | Constraints eqs ->
    Constraints { eqs with data = ModId.update id desc eqs.data }

let best_path_of_list = function
  | [] -> assert false
  | p :: tl ->
    let path_score p =
      if Path.rigid p then 3 else
      if Ident.rigid (Path.first p) then 2 else 1
    in
    let rec aux best_p score = function
      | [] -> best_p
      | p :: tl ->
        let score' = path_score p in
        if score' > score then
          aux p score' tl
        else
          aux best_p score tl
    in
    aux p (path_score p) tl

let rec update_path_name path acc eqs id =
  match eqs with
  | HasContradiction -> id, [], HasContradiction
  | Constraints { data } ->
    let info = ModId.find id data in
    match info.mi_desc with
    | Alias id -> update_path_name path acc eqs id
    | BaseType _ ->
      id, (Type, path, info.mi_path) :: acc, eqs
    | _ ->
      id, (Module, path, info.mi_path) :: acc, eqs

let rec merge_ids ?path acc eqs id1 id2 =
  if id1 = id2 then id1, acc, eqs else
  match eqs with
  | HasContradiction -> id1, [], HasContradiction
  | Constraints { data } ->
  let info1 = ModId.find id1 data
  and info2 = ModId.find id2 data in
  let mi_path =
    best_path_of_list begin
      match path with
      | Some p -> [p; info1.mi_path; info2.mi_path]
      | None -> [info1.mi_path; info2.mi_path]
    end
  in
  let id, acc, eqs =
    match info1.mi_desc, info2.mi_desc with
    | Alias id1, Alias id2 -> merge_ids ?path acc eqs id1 id2
    | Alias id1, _ -> merge_ids ?path acc eqs id1 id2
    | _, Alias id2 -> merge_ids ?path acc eqs id1 id2
    | Mod, _ -> id2, (Module, info1.mi_path, info2.mi_path) :: acc, eqs
    | _, Mod -> id1, (Module, info1.mi_path, info2.mi_path) :: acc, eqs
    (* | Equalities _, _ | _, Equalities _ -> assert false *)
    | App app1, App app2 ->
      let quantified_apps = app1.quantified_apps @ app2.quantified_apps in
      let eqs_ref = ref eqs and acc = ref acc in
      let static_apps =
        Path.Map.merge
          (fun parg i1 i2 ->
            merge_ids' (Path.Papply (mi_path, parg)) acc eqs_ref i1 i2)
          app1.static_apps app2.static_apps
      in
      let eqs =
        update_eqs id1
          { mi_path; mi_desc = App { static_apps; quantified_apps }; }
          !eqs_ref
      in
      id1, (Module, info1.mi_path, info2.mi_path) :: !acc, eqs
    | Projections projs1, Projections projs2 ->
      let eqs_ref = ref eqs and acc = ref acc in
      let projs =
        SMap.merge
          (fun s i1 i2 -> merge_ids' (Path.Pdot (mi_path, s)) acc eqs_ref i1 i2)
          projs1 projs2
      in
      let eqs =
        update_eqs id1 { mi_path; mi_desc = Projections projs; } !eqs_ref
      in
      id1, (Module, info1.mi_path, info2.mi_path) :: !acc, eqs
    | ExtraProjs projs1, ExtraProjs projs2 ->
      let eqs_ref = ref eqs and acc = ref acc in
      let projs =
        EtyMap.merge
          (fun ety i1 i2 ->
            merge_ids' (Path.Pextra_ty (mi_path, ety)) acc eqs_ref i1 i2)
          projs1 projs2
      in
      let eqs =
        update_eqs id1 { mi_path; mi_desc = ExtraProjs projs; } !eqs_ref
      in
      id1, (Module, info1.mi_path, info2.mi_path) :: !acc, eqs
    | BaseType l1, BaseType l2 ->
      let eqs =
        update_eqs id1 { mi_path; mi_desc = BaseType (l1 @ l2); } eqs
      in
      id1, (Type, info1.mi_path, info2.mi_path) :: acc, eqs
    | BaseType _, (App _ | Projections _ | ExtraProjs _)
    | App _, (BaseType _ | Projections _ | ExtraProjs _)
    | Projections _, (BaseType _ | App _ | ExtraProjs _)
    | ExtraProjs _, (BaseType _ | App _ | Projections _) ->
      id1, [], HasContradiction
  in
  (* TODO : add eq between info1.mi_path and info2.mi_path *)
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
    let id, acc', eqs' = update_path_name path acc' eqs' id in
    eqs := eqs';
    acc := acc';
    Some id
  | Some id, None | None, Some id ->
    let id, acc', eqs' = update_path_name path !acc !eqs id in
    eqs := eqs';
    acc := acc';
    Some id
  | None, None -> assert false (* Should not happen *)

let rec merge_path_ids env eqs id1 id2 =
  let _, acc, eqs = merge_ids [] eqs id1 id2 in
  List.fold_left (fun eqs (k, p1, p2) -> merge_paths env k p1 p2 eqs) eqs acc
and merge_paths env eq_kind p1 p2 eqs =
  match eqs with
  | HasContradiction -> HasContradiction
  | Constraints eqs ->
    match eq_kind with
    | Module ->
      let p1 = normalize_module_path env eqs p1
      and p2 = normalize_module_path env eqs p2 in
      merge_paths_normalized env Module p1 p2 eqs
    | Type ->
      let p1, oty1 = normalize_type_path env eqs p1
      and p2, oty2 = normalize_type_path env eqs p2 in
      match oty1, oty2 with
      | None, None ->
        merge_paths_normalized env Type p1 p2 eqs
      | None, Some ty ->
        let eqs = maybe_merge_paths_normalized env Type p1 p2 eqs in
        add_path_type_eq env [] p1 [] ty eqs
      | Some ty, None ->
        let eqs = maybe_merge_paths_normalized env Type p1 p2 eqs in
        add_path_type_eq env [] p2 [] ty eqs
      | Some ty1, Some ty2 ->
        let eqs = maybe_merge_paths_normalized env Type p1 p2 eqs in
        add_type_type_eq env ~env_params:env [] ty1 ty2 eqs
and maybe_merge_paths_normalized env eq_kind p1 p2 eqs =
  if Ident.rigid (Path.first p1) && Ident.rigid (Path.first p2) then
    Constraints eqs
  else
    merge_paths_normalized env eq_kind p1 p2 eqs
and merge_paths_normalized env eq_kind p1 p2 eqs =
  match Ident.rigid (Path.first p1), Ident.rigid (Path.first p2) with
  | true, true ->
    begin match Path.merge p1 p2 with
      | Some sub_eqs ->
        List.fold_left
          (fun eqs (p1, p2) -> merge_paths env Module p1 p2 eqs)
          (Constraints eqs) sub_eqs
      | None ->
        HasContradiction
    end
  | false, false ->
    begin
      let id1, eqs, final_arg1 = get_path_target eqs p1 eq_kind [] in
      let id2, eqs, final_arg2 = get_path_target eqs p2 eq_kind [] in
      match final_arg1, final_arg2 with
      | None, None -> merge_path_ids env (Constraints eqs) id1 id2
      | _, _ -> assert false (* TODO *)
    end
  | true, false ->
    begin
      let id2, eqs, final_arg2 = get_path_target eqs p2 eq_kind [] in
      match final_arg2 with
      | None ->
        let info = ModId.find id2 eqs.data in
        assert (info.mi_path = p2);
        Constraints { eqs with
          data = ModId.update id2 {info with mi_path = p1} eqs.data
        }
      | _ -> assert false (* TODO *)
    end
  | false, true ->
    begin
      let id1, eqs, final_arg1 = get_path_target eqs p1 eq_kind [] in
      match final_arg1 with
      | None ->
        let info = ModId.find id1 eqs.data in
        assert (info.mi_path = p1);
        Constraints { eqs with
          data = ModId.update id1 {info with mi_path = p2} eqs.data
        }
      | _ -> assert false (* TODO *)
    end
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
      assert (params = []);
      merge_paths env Type p1 p2 (Constraints eqs)
    (* | Tconstr (p2, tyl2, _) ->
      let id, eqs, final_arg = get_path_target eqs p1 Type params in
      let p1 =
        Env.normalize_type_path (Some Location.none) env
          (Path.subst_map eqs.solved_flex p1)
      in
      let p2 =
        Env.normalize_type_path (Some Location.none) env
          (Path.subst_map eqs.solved_flex p2)
      in
      let path1 = to_path_with_head p1 and path2 = to_path_with_head p2 in
      begin match Ident.rigid path1.first, Ident.rigid path2.first with
      | true, true ->
        add_type_type_eq env ~env_params params
          (Btype.newgenty (Tconstr (p1, tyl1, ref Types.Mnil)))
          (Btype.newgenty (Tconstr (p2, tyl2, ref Types.Mnil)))
          (Constraints eqs)
      | false, false ->
        let type_eq = PathEqPath {
            params;
            path_flex1 = path1; tyl1;
            path_flex2 = path2; tyl2
        } in
        Constraints(add_eq path2.first type_eq (add_eq path1.first type_eq eqs))
      | false, true ->
        let type_eq =
          PathEqType { params; path_flex = path1; tyl = tyl1; ty2 }
        in
        Constraints (add_eq path1.first type_eq eqs)
      | true, false ->
        let ty1 = Btype.newgenty (Tconstr (p1, tyl1, ref Types.Mnil)) in
        let type_eq =
          PathEqType { params; path_flex = path2; tyl = tyl2; ty2 = ty1 }
        in
        Constraints (add_eq path2.first type_eq eqs)
      end *)
    | _ ->
      let p1 =
        Env.normalize_type_path (Some Location.none) env (path_subst_map env eqs p1)
      in
      if Ident.rigid (Path.first p1) then
        add_type_type_eq env ~env_params params
          (Btype.newgenty (Tconstr (p1, tyl1, ref Types.Mnil))) ty2
          (Constraints eqs)
      else
        let id, eqs, final_arg = get_path_target eqs p1 Type params in
        (* match eqs with
        | HasContradiction -> HasContradiction
        | Constraints eqs -> *)
          match final_arg with
          | Some _ -> assert false (* TODO *)
          | None ->
            let info = ModId.find id eqs.data in
            match info.mi_desc with
            | BaseType cstrs ->
              Constraints { eqs with
                data =
                  ModId.update id
                    {info with mi_desc = BaseType ((tyl1, ty2) :: cstrs) }
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
          let () = assert (params = []) in
          match merge_paths env Type p1 p2 eqs with
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
  && Ident.Map.is_empty eqs.type_constraints

(* let solve_opt env k i p = function
  | HasContradiction -> HasContradiction
  | Constraints eqs -> solve env ~env_params:env k [] i p eqs *)

let merge env eqs1 eqs2 =
  let type_constraints =
      Ident.Map.union
        (fun _i x y -> Some (List.append x y))
        eqs1.type_constraints eqs2.type_constraints
  in
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
    (Constraints { type_constraints; data; flex_heads })
    !pairs

let merge env eqs1 eqs2 =
  match eqs1, eqs2 with
  | HasContradiction, _ | _, HasContradiction -> HasContradiction
  | Constraints eqs1, Constraints eqs2 ->
    if is_empty eqs1 then Constraints eqs2 else begin
      if is_empty eqs2 then Constraints eqs1 else begin
        merge env eqs1 eqs2
      end
    end

let is_empty = function
  | Constraints eqs -> is_empty eqs
  | HasContradiction -> false

(* let merge env eqs1 eqs2 =
  let res = merge env eqs1 eqs2 in
  if not (is_empty eqs1) && not (is_empty eqs2) then
    Format.eprintf "Merge : %a\n%a\n ==> %a\n"
      (Format_doc.compat print) eqs1
      (Format_doc.compat print) eqs2
      (Format_doc.compat print) res;
  res *)

let incompatible = ref (fun _ _ _ -> assert false)

let has_error_type_constraints env eqs =
  let base_type_abs path = function
    | BaseType cstrs ->
      let rec aux = function
        | [] -> false
        | (tyl, ty) :: tl ->
          !incompatible env (Btype.newgenty (Tconstr (path, tyl, ref Types.Mnil))) ty
          || (if tyl = [] then List.exists (function ([], ty2) -> !incompatible env ty ty2 | _ -> false) tl else false)
          || aux tl
      in aux cstrs
    | _ -> false
  in
  let rec has_contra p1 tyl1 ty1 = function
    | [] -> false
    | PathEqType { params = []; path_flex = p2; tyl = []; ty2 } :: tl ->
      begin
        let p2, oty = normalize_type_path env eqs p2.path in
        match oty with
        | None ->
          Path.same p1 p2 && !incompatible env ty1 ty2
        | Some ty_p2 ->
          !incompatible env ty_p2 ty2
      end || has_contra p1 tyl1 ty1 tl
    | PathEqType { params = []; path_flex = p2; tyl = tyl2; ty2 } :: tl ->
      if Path.same p1 p2.path
          && List.for_all2 (fun ty1 ty2 -> not (!incompatible env ty1 ty2)) tyl1 tyl2
      then begin
        !incompatible env ty1 ty2 || has_contra p1 tyl1 ty1 tl
      end
      else has_contra p1 tyl1 ty1 tl
    | _ :: tl -> has_contra p1 tyl1 ty1 tl
  in
  let rec has_error_one = function
    | [] -> false
    | PathEqType { params = []; path_flex; tyl = []; ty2 = ty } :: tl ->
      begin
        let p, oty = normalize_type_path env eqs path_flex.path in
        match oty with
        | None ->
          !incompatible env (Btype.newgenty (Tconstr (p, [], ref Types.Mnil))) ty || has_contra p [] ty tl
        | Some ty' ->
          !incompatible env ty ty'
      end || has_error_one tl
    | PathEqType { params = []; path_flex; tyl; ty2 } :: tl ->
      has_contra path_flex.path tyl ty2 tl || has_error_one tl
    | _ :: tl -> has_error_one tl
  in
  ModId.exists (fun _ info -> base_type_abs info.mi_path info.mi_desc) eqs.data
  || Ident.Map.exists (fun _ l -> has_error_one l) eqs.type_constraints

let has_error env = function
  | HasContradiction -> true
  | Constraints eqs ->
    has_error_type_constraints env eqs

(* let same_freeness id {pp_params; pp_rigid; pp_flex} =
  List.exists (fun (id', _) -> Ident.same id id') pp_params
  || Path.exists_free [id] pp_rigid.path = Path.exists_free [id] pp_flex.path *)

let generalize _env param eqs =
  match param, eqs with
  | Types.Unit, _ | Types.Named (_, None, _), _ | _, HasContradiction -> eqs
  | Types.Named (_, Some _id, _mty), Constraints eqs ->
    assert (is_empty (Constraints eqs));
    Constraints eqs
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

let add_path_eq env eq_kind p1 p2 eqs = merge_paths env eq_kind p1 p2 eqs
let add_path_type_eq env p tyl ty eqs =
  match tyl, Types.get_desc ty with
  | [], Tconstr (p2, [], _) -> add_path_eq env Type p p2 eqs
  | _ -> add_path_type_eq env [] p tyl ty eqs
