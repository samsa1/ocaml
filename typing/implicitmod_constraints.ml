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
  first : Ident.t;
}

type params = (Ident.t * Types.module_type) list

type path_pair = {
  eq_kind : path_eq_kind;
  pp_params : params;
  pp_rigid : path_with_head;
  pp_flex : path_with_head;
}

let build_path_pair eq_kind pp_params ~rigid:pp_rigid ~flex:pp_flex =
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
  {eq_kind; pp_params = filter_params pp_params; pp_rigid; pp_flex}

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

type t_inner = {
  flex_flex : (path_eq_kind * params * path_with_head * path_with_head) list;
  flex_rigid_heads : path_pair list Ident.Map.t;
  solved_flex : Path.t Ident.Map.t;
  type_constraints : type_constraint list Ident.Map.t;
}

type t =
  | HasContradiction
  | Constraints of t_inner

let empty = Constraints {
  flex_flex = [];
  flex_rigid_heads = Ident.Map.empty;
  solved_flex = Ident.Map.empty;
  type_constraints = Ident.Map.empty;
}

let to_path_with_head path =
  { path = path; first = Path.first path }


let expand_head_rigid = ref (fun _ _ -> assert false)

let type_expr_printer = ref (fun _ _ -> assert false)

module Pp = struct
  let print_params fmt params =
    Format_doc.fprintf fmt "[%a]"
      (Format_doc.pp_print_list
        (fun fmt (id, _) -> Format_doc.pp_print_string fmt (Ident.name id)))
      params

  let print_pair fmt (k, params, p1, p2) =
    Format_doc.fprintf fmt "@[<hov2>%a@ %a@ =%s@ %a@]"
      print_params params
      Path.print p1.path
      (match k with Module -> "m" | Type -> "t")
      Path.print p2.path

  let print_path_pair fmt {eq_kind; pp_params; pp_rigid; pp_flex} =
    Format_doc.fprintf fmt "@[<hov2>%a@ %a@ =%s@ %a@]"
      print_params pp_params
      Path.print pp_rigid.path
      (match eq_kind with Module -> "m" | Type -> "t")
      Path.print pp_flex.path

  let pp_flex_flex fmt flex_flex =
    Format_doc.fprintf fmt "@[<hov>flex_flex = %a@]"
      (Format_doc.pp_print_list print_pair) flex_flex

  let pp_rigid_heads fmt flex_rigid_heads =
    let aux fmt i pairs =
      Format_doc.fprintf fmt "%s =>@ %a\n"
        (Ident.name i)
        (Format_doc.pp_print_list print_path_pair) pairs
    in
    Format_doc.fprintf fmt "@[<hov>flex_rigid_heads = %a@]"
      (fun fmt -> Ident.Map.iter (aux fmt)) flex_rigid_heads

  let pp_solved_flex fmt solved_flex =
    let aux fmt i p =
      Format_doc.fprintf fmt "@[%s = %a@]\n"
        (Ident.name i)
        Path.print p
    in
    Format_doc.fprintf fmt "@[<hov>solved_flex = %a@]"
      (fun fmt -> Ident.Map.iter (aux fmt)) solved_flex

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
    Format_doc.fprintf fmt "@[<hov2>{%a;@ %a;@ %a;@ %a}@]"
      pp_flex_flex eqs.flex_flex
      pp_rigid_heads eqs.flex_rigid_heads
      pp_solved_flex eqs.solved_flex
      pp_type_constraints eqs.type_constraints
end

let print fmt eqs =
  match eqs with
  | Constraints eqs -> Pp.print_inner fmt eqs
  | HasContradiction -> Format_doc.fprintf fmt "Absurd"

type path_or_manifest =
  | PM_Path of Path.t
  | PM_Manifest of Types.type_expr

let rec normalize_type_path env p =
  try
    let (params, ty, _) = Env.find_type_expansion p env in
    assert (params = []);
    match Types.get_desc ty with
    | Tconstr (p, [], _) ->
      normalize_type_path env p
    | _ -> PM_Manifest ty
  with
    Not_found -> PM_Path (Env.normalize_type_path (Some Location.none) env p)

let rec split_flex_flex env i p still_flex flexibility_changed = function
  | [] -> still_flex, flexibility_changed
  | (k, params, p1, p2) :: tl ->
    let p1 = { p1 with path = Path.subst [(i, p)] p1.path }
    and p2 = { p2 with path = Path.subst [(i, p)] p2.path } in
    let still_flex, flexibility_changed =
      if Ident.same p1.first i || Ident.same p2.first i then
        match k with
        | Module ->
          let p1 = Env.normalize_module_path (Some Location.none) env p1.path
          and p2 = Env.normalize_module_path (Some Location.none) env p2.path
          in
          still_flex, (Module, params, p1, p2) :: flexibility_changed
        | Type ->
          (* TODO : Should normalize type paths here instead of forgetting them
            see normalize_type_path in printer *)
          still_flex, flexibility_changed
      else
        (k, params, p1, p2) :: still_flex, flexibility_changed
    in
    split_flex_flex env i p still_flex flexibility_changed tl

let rec split_rigid_flex env i p still_flex flexibility_changed = function
  | [] -> still_flex, flexibility_changed
  | {eq_kind; pp_params; pp_rigid; pp_flex} :: tl ->
    let pp_rigid = { pp_rigid with path = Path.subst [(i, p)] pp_rigid.path }
    and pp_flex = { pp_flex with path = Path.subst [(i, p)] pp_flex.path } in
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
    let path_flex =
      { path_flex with path = Path.subst [(i, p)] path_flex.path }
    in
    let still_flex, flexibility_changed =
      if Ident.same path_flex.first i then
        still_flex, (params, path_flex.path, tyl, ty2) :: flexibility_changed
      else
        PathEqType {params; path_flex; tyl; ty2 } :: still_flex,
          flexibility_changed
    in
    split_path_type_eq env i p still_flex flexibility_changed tl
  | PathEqPath {params; path_flex1; tyl1; path_flex2; tyl2 } :: tl ->
    let path_flex1 =
      { path_flex1 with path = Path.subst [(i, p)] path_flex1.path }
    and path_flex2 =
      { path_flex2 with path = Path.subst [(i, p)] path_flex2.path }
    in
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
    split_path_type_eq env i p still_flex flexibility_changed tl

let add_eq id type_eq eqs =
  let els =
    match Ident.Map.find id eqs.type_constraints with
    | els -> els
    | exception Not_found -> []
  in
  let type_constraints =
    Ident.Map.add id (type_eq :: els) eqs.type_constraints
  in
  { eqs with type_constraints }

let rec add_pair env pair eqs =
  assert (not (Ident.rigid pair.pp_flex.first));
  let pairs =
    match Ident.Map.find pair.pp_flex.first eqs.flex_rigid_heads with
    | pairs -> pairs
    | exception Not_found -> []
  in
  match
    List.find_opt (fun p2 -> pair.pp_params = []
                            && p2.pp_params = []
                            && (Path.same pair.pp_rigid.path p2.pp_rigid.path
                                || Path.same pair.pp_flex.path p2.pp_flex.path))
                              pairs
  with
  | Some p2 when Path.same pair.pp_rigid.path p2.pp_rigid.path ->
    add_pp_normalizing env ~env_params:env p2.eq_kind []
        pair.pp_flex.path p2.pp_flex.path eqs
  | Some p2 ->
    add_pp_normalizing env ~env_params:env p2.eq_kind []
        pair.pp_rigid.path p2.pp_rigid.path eqs
  | None ->
    Constraints { eqs with
        flex_rigid_heads =
          Ident.Map.add pair.pp_flex.first (pair :: pairs) eqs.flex_rigid_heads
    }
and add_path_eq env ?env_params eq_kind params p1 p2 = function
  | HasContradiction -> HasContradiction
  | Constraints eqs ->
    let env_params =
      match env_params with
      | Some env_params -> env_params
      | None ->
        List.fold_left
          (fun env (id, mty) -> Env.add_module id Mp_present IILocal mty env)
          env params
    in
    add_pp_normalizing env ~env_params eq_kind params p1 p2 eqs
and add_pp_normalizing env ~env_params eq_kind params p1 p2 eqs =
  let p1 = Path.subst_map eqs.solved_flex p1
  and p2 = Path.subst_map eqs.solved_flex p2 in
  match eq_kind with
  | Module ->
    add_pp_normalized env ~env_params eq_kind params
      (Env.normalize_module_path (Some Location.none) env p1)
      (Env.normalize_module_path (Some Location.none) env p2)
      eqs
  | Type ->
    let op1 = normalize_type_path env p1
    and op2 = normalize_type_path env p2 in
    match op1, op2 with
    | PM_Path p1, PM_Path p2 ->
      add_pp_normalized env ~env_params eq_kind params p1 p2 eqs
    | PM_Path p, PM_Manifest ty
    | PM_Manifest ty, PM_Path p ->
      begin
        match Types.get_desc ty with
        | Tconstr (_, [], _) -> assert false
        | _ -> ()
      end;
      add_path_type_eq env ~env_params params p [] ty (Constraints eqs)
    | PM_Manifest ty1, PM_Manifest ty2 ->
      add_type_type_eq env ~env_params params ty1 ty2 (Constraints eqs)
and add_pp_normalized env ~env_params eq_kind params p1 p2 eqs =
  match p1, p2 with
  | Path.Pident i, _ when not (Ident.rigid i) ->
    solve env ~env_params eq_kind params i p2 eqs
  | _, Path.Pident i when not (Ident.rigid i) ->
    solve env ~env_params eq_kind params i p1 eqs
  | _, _ ->
    let p1 = to_path_with_head p1
    and p2 = to_path_with_head p2 in
    match Ident.rigid p1.first, Ident.rigid p2.first with
    | true, true ->
      begin match Path.merge p1.path p2.path with
        | Some sub_eqs ->
          List.fold_left
            (fun eqs (p1, p2) ->
                add_path_eq env ~env_params Module params p1 p2 eqs)
            (Constraints eqs) sub_eqs
        | None ->
          HasContradiction
      end
    | true, false ->
      add_pair env (build_path_pair eq_kind params ~rigid:p1 ~flex:p2)
        eqs
    | false, true ->
      add_pair env (build_path_pair eq_kind params ~rigid:p2 ~flex:p1)
        eqs
    | false, false ->
      Constraints {eqs with flex_flex = (eq_kind, params, p1, p2) :: eqs.flex_flex }
and solve env ~env_params eq_kind params i p eqs =
  match p with
  | Path.Pident i2 when Ident.same i i2 -> Constraints eqs
  | _ ->
    assert (eq_kind = Module);
    match Ident.Map.find_opt i eqs.solved_flex with
    | None ->
      solve_unsolved env params i p eqs
    | Some p2 ->
      add_pp_normalizing env ~env_params eq_kind params p p2 eqs
and solve_unsolved env params i p eqs =
  assert (not (Ident.rigid i));
  assert (params = []);
  let flex_flex, to_handle = split_flex_flex env i p [] [] eqs.flex_flex in
  let solved_flex =
    Ident.Map.add i p (Ident.Map.map (Path.subst [(i, p)]) eqs.solved_flex)
  in
  let flex_rigid_heads, to_handle =
    Ident.Map.fold
      (fun k pairs (map, to_handle) ->
        let pairs', to_handle = split_rigid_flex env i p [] to_handle pairs in
        let map =
          if pairs' = [] then
            map
          else
            Ident.Map.add k pairs' map
        in (map, to_handle)
      )
      eqs.flex_rigid_heads (Ident.Map.empty, to_handle)
  in
  let type_constraints, to_handle_ty =
    Ident.Map.fold
      (fun k constraints_list (map, to_handle) ->
        let constraints_list', to_handle =
          split_path_type_eq env i p [] to_handle constraints_list
        in
        let map =
          if constraints_list' = [] then
            map
          else Ident.Map.add k constraints_list' map
        in (map, to_handle))
      eqs.type_constraints (Ident.Map.empty, [])
  in
  let eqs =
    List.fold_left
      (fun eqs (k, params, p1, p2) -> add_path_eq env k params p1 p2 eqs)
      (Constraints {flex_flex; solved_flex; flex_rigid_heads; type_constraints})
      to_handle
  in
  List.fold_left
    (fun eqs (params, p, tyl, ty) -> add_path_type_eq env params p tyl ty eqs)
    eqs
    to_handle_ty
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
    match Types.get_desc ty2, tyl1 with
    | Tconstr (p2, [], _), [] ->
      add_pp_normalizing env ~env_params Type params p1 p2 eqs
    | Tconstr (p2, tyl2, _), _ ->
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
      end
    | _, _ ->
      let p1 =
        Env.normalize_type_path (Some Location.none) env
          (Path.subst_map eqs.solved_flex p1)
      in
      let path1 = to_path_with_head p1 in
      if Ident.rigid path1.first then
        add_type_type_eq env ~env_params params
          (Btype.newgenty (Tconstr (p1, tyl1, ref Types.Mnil))) ty2
          (Constraints eqs)
      else
        let type_eq =
          PathEqType { params; path_flex = path1; tyl = tyl1; ty2 }
        in
        Constraints (add_eq path1.first type_eq eqs)
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
          match add_path_eq env ~env_params Type params p1 p2 eqs with
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
  eqs.flex_flex = []
  && Ident.Map.is_empty eqs.flex_rigid_heads
  && Ident.Map.is_empty eqs.solved_flex
  && Ident.Map.is_empty eqs.type_constraints

let solve_opt env k i p = function
  | HasContradiction -> HasContradiction
  | Constraints eqs -> solve env ~env_params:env k [] i p eqs

let merge env eqs1 eqs2 =
  match
    Ident.Map.fold (solve_opt env Module) eqs1.solved_flex (Constraints eqs2)
  with
  | HasContradiction -> HasContradiction
  | Constraints eqs2 ->
    let type_constraints =
        Ident.Map.merge
          (fun _i x y ->
            match x, y with
            | None, None -> None
            | Some x, None | None, Some x -> Some x
            | Some x, Some y -> Some (List.append x y))
          eqs1.type_constraints eqs2.type_constraints
    in
    let eqs1 = { eqs1 with type_constraints } in
    let eqs =
      List.fold_left
        (fun eqs (k, params, p1, p2) ->
            add_path_eq env k params p1.path p2.path eqs)
        (Constraints eqs1) eqs2.flex_flex
    in
    let eqs =
      Ident.Map.fold
        (fun _ pl eqs ->
            List.fold_left
              (fun eqs {eq_kind; pp_params; pp_flex; pp_rigid} ->
                add_path_eq env eq_kind pp_params pp_rigid.path pp_flex.path eqs)
              eqs pl)
        eqs2.flex_rigid_heads
        eqs
    in Ident.Map.fold (solve_opt env Module) eqs2.solved_flex eqs

let merge env eqs1 eqs2 =
  match eqs1, eqs2 with
  | HasContradiction, _ | _, HasContradiction -> HasContradiction
  | Constraints eqs1, Constraints eqs2 ->
    if is_empty eqs1 then Constraints eqs2 else begin
      if is_empty eqs2 then Constraints eqs1 else begin
        if Ident.Map.is_empty eqs1.solved_flex then
          merge env eqs1 eqs2
        else
          merge env eqs2 eqs1
      end
    end

let is_empty = function
  | Constraints eqs -> is_empty eqs
  | HasContradiction -> false

(* let has_error_type_constraints env eqs =
  let rec has_contra p ty = function
    | [] -> false
    | ([], p2, [], ty2) :: tl ->
      begin
        match
          normalize_type_path env (Path.subst_map eqs.solved_flex p2.path)
        with
        | PM_Path p2 ->
          if Path.same p p2 then
            !incompatible env ty ty2
          else false
        | PM_Manifest ty_p2 -> !incompatible env ty_p2 ty2
      end || has_contra p ty tl
    | _ :: tl -> has_contra p ty tl
  in
  let rec has_error_one = function
    | [] -> false
    | ([], p, [], ty) :: tl ->
      begin
        match
          normalize_type_path env (Path.subst_map eqs.solved_flex p.path)
        with
        | PM_Path p ->
          !incompatible env (Btype.newgenty (Tconstr (p, [], ref Types.Mnil))) ty || has_contra p ty tl
        | PM_Manifest ty' -> !incompatible env ty ty'
      end || has_error_one tl
    | _ :: tl -> has_error_one tl
  in
  Ident.Map.exists (fun _ l -> has_error_one l) eqs.type_constraints *)

let has_error _env = function
  | HasContradiction -> true
  | Constraints _eqs -> false
    (* let b = has_error_type_constraints env eqs in
    Format.eprintf "has_error?%b in\n%a\n\n"
      b
      (Format_doc.compat print) (Constraints eqs);
    b *)

let same_freeness id {pp_params; pp_rigid; pp_flex} =
  List.exists (fun (id', _) -> Ident.same id id') pp_params
  || Path.exists_free [id] pp_rigid.path = Path.exists_free [id] pp_flex.path

let generalize _env param eqs =
  match param, eqs with
  | Types.Unit, _ | Types.Named (_, None, _), _ | _, HasContradiction -> eqs
  | Types.Named (_, Some id, mty), Constraints eqs ->
    if Ident.Map.exists (fun _ p -> Path.exists_free [id] p) eqs.solved_flex
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
    end

let add_path_eq env eq_kind p1 p2 eqs = add_path_eq env eq_kind [] p1 p2 eqs
let add_path_type_eq env p tyl ty eqs = add_path_type_eq env [] p tyl ty eqs
