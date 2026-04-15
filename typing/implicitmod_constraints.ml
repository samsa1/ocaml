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

type path_pair = {
  eq_kind : path_eq_kind;
  pp_rigid : path_with_head;
  pp_flex : path_with_head;
}

type t_inner = {
  flex_flex : (path_eq_kind * path_with_head * path_with_head) list;
  rigid_heads : path_pair list Ident.Map.t;
  solved_flex : Path.t Ident.Map.t;
  type_constraints : (Path.t * Types.type_expr list * Types.type_expr) list Ident.Map.t;
}

type t = t_inner option

let empty = Some {
  flex_flex = [];
  rigid_heads = Ident.Map.empty;
  solved_flex = Ident.Map.empty;
  type_constraints = Ident.Map.empty;
}

let to_path_with_head path =
  { path = path; first = Path.first path }



let incompatible = ref (fun _ _ _ -> assert false)

let type_expr_printer = ref (fun _ _ -> assert false)

module Pp = struct
  let print_pair fmt (k, p1, p2) =
    Format_doc.fprintf fmt "@[<hov2>%a@ =%s@ %a@]"
      Path.print p1.path
      (match k with Module -> "m" | Type -> "t")
      Path.print p2.path

  let print_path_pair fmt {eq_kind; pp_rigid; pp_flex} =
    Format_doc.fprintf fmt "@[<hov2>%a@ =%s@ %a@]"
      Path.print pp_rigid.path
      (match eq_kind with Module -> "m" | Type -> "t")
      Path.print pp_flex.path

  let pp_flex_flex fmt flex_flex =
    Format_doc.fprintf fmt "@[<hov>flex_flex = %a@]"
      (Format_doc.pp_print_list print_pair) flex_flex

  let pp_rigid_heads fmt rigid_heads =
    let aux fmt i pairs =
      Format_doc.fprintf fmt "%s =>@ %a\n"
        (Ident.name i)
        (Format_doc.pp_print_list print_path_pair) pairs
    in
    Format_doc.fprintf fmt "@[<hov>rigid_heads = %a@]"
      (fun fmt -> Ident.Map.iter (aux fmt)) rigid_heads

  let pp_solved_flex fmt solved_flex =
    let aux fmt i p =
      Format_doc.fprintf fmt "@[%s = %a@]\n"
        (Ident.name i)
        Path.print p
    in
    Format_doc.fprintf fmt "@[<hov>solved_flex = %a@]"
      (fun fmt -> Ident.Map.iter (aux fmt)) solved_flex

  let print_one_type_eq fmt (p, tyl, ty) =
      Format_doc.fprintf fmt "%a(%a) => %a\n"
        Path.print p
        (Format_doc.pp_print_list !type_expr_printer) tyl
        !type_expr_printer ty

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
      pp_rigid_heads eqs.rigid_heads
      pp_solved_flex eqs.solved_flex
      pp_type_constraints eqs.type_constraints
end

let print fmt eqs =
  match eqs with
  | Some eqs -> Pp.print_inner fmt eqs
  | None -> Format_doc.fprintf fmt "Absurd"

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

let add_pair pair eqs =
  assert (Ident.rigid pair.pp_rigid.first);
  let pairs =
    match Ident.Map.find pair.pp_rigid.first eqs.rigid_heads with
    | pairs -> pairs
    | exception Not_found -> []
  in
  { eqs with
      rigid_heads =
        Ident.Map.add pair.pp_rigid.first (pair :: pairs) eqs.rigid_heads
  }

let rec split_flex_flex env i p still_flex flexibility_changed = function
  | [] -> still_flex, flexibility_changed
  | (k, p1, p2) :: tl ->
    let p1 = { p1 with path = Path.subst [(i, p)] p1.path }
    and p2 = { p2 with path = Path.subst [(i, p)] p2.path } in
    let still_flex, flexibility_changed =
      if Ident.same p1.first i || Ident.same p2.first i then
        match k with
        | Module ->
          let p1 = Env.normalize_module_path (Some Location.none) env p1.path
          and p2 = Env.normalize_module_path (Some Location.none) env p2.path
          in
          still_flex, (Module, p1, p2) :: flexibility_changed
        | Type ->
          (* TODO : Should normalize type paths here instead of forgetting them
            see normalize_type_path in printer *)
          still_flex, flexibility_changed
      else
        (k, p1, p2) :: still_flex, flexibility_changed
    in
    split_flex_flex env i p still_flex flexibility_changed tl

let rec split_rigid_flex env i p still_flex flexibility_changed = function
  | [] -> still_flex, flexibility_changed
  | {eq_kind; pp_rigid; pp_flex} :: tl ->
    let pp_rigid = { pp_rigid with path = Path.subst [(i, p)] pp_rigid.path }
    and pp_flex = { pp_flex with path = Path.subst [(i, p)] pp_flex.path } in
    let still_flex, flexibility_changed =
      if Ident.same pp_flex.first i then
        still_flex,
          (eq_kind, pp_rigid.path, pp_flex.path) :: flexibility_changed
      else
        {eq_kind; pp_rigid; pp_flex} :: still_flex, flexibility_changed
    in
    split_rigid_flex env i p still_flex flexibility_changed tl

let rec add_path_eq env eq_kind p1 p2 eqs =
  Option.bind eqs (add_pp_normalizing env eq_kind p1 p2)
and add_pp_normalizing env eq_kind p1 p2 eqs =
  let p1 = Path.subst_map eqs.solved_flex p1
  and p2 = Path.subst_map eqs.solved_flex p2 in
  match eq_kind with
  | Module ->
    add_pp_normalized env eq_kind
      (Env.normalize_module_path (Some Location.none) env p1)
      (Env.normalize_module_path (Some Location.none) env p2)
      eqs
  | Type ->
    let op1 = normalize_type_path env p1
    and op2 = normalize_type_path env p2 in
    match op1, op2 with
    | PM_Path p1, PM_Path p2 ->
      add_pp_normalized env eq_kind p1 p2 eqs
    | PM_Path p, PM_Manifest ty
    | PM_Manifest ty, PM_Path p ->
      begin
        match Types.get_desc ty with
        | Tconstr (_, [], _) -> assert false
        | _ -> ()
      end;
      add_pt_normalized env p [] ty eqs
    | PM_Manifest ty1, PM_Manifest ty2 ->
      add_type_type_eq env ty1 ty2 eqs
and add_pp_normalized env eq_kind p1 p2 eqs =
  match p1, p2 with
  | Path.Pident i, _ when not (Ident.rigid i) ->
    solve env eq_kind i p2 eqs
  | _, Path.Pident i when not (Ident.rigid i) ->
    solve env eq_kind i p1 eqs
  | _, _ ->
    let p1 = to_path_with_head p1
    and p2 = to_path_with_head p2 in
    match Ident.rigid p1.first, Ident.rigid p2.first with
    | true, true ->
      begin match Path.merge p1.path p2.path with
        | Some sub_eqs ->
          List.fold_left
            (fun eqs (p1, p2) -> add_path_eq env Module p1 p2 eqs)
            (Some eqs) sub_eqs
        | None -> None
      end
    | true, false ->
      Some (add_pair {eq_kind; pp_rigid = p1; pp_flex = p2} eqs)
    | false, true ->
      Some (add_pair {eq_kind; pp_rigid = p2; pp_flex = p1} eqs)
    | false, false ->
      Some {eqs with flex_flex = (eq_kind, p1, p2) :: eqs.flex_flex }
and solve env eq_kind i p eqs =
  match p with
  | Path.Pident i2 when Ident.same i i2 -> Some eqs
  | _ ->
    assert (eq_kind = Module);
    match Ident.Map.find_opt i eqs.solved_flex with
    | None ->
      solve_unsolved env i p eqs
    | Some p2 ->
      add_path_eq env eq_kind p p2 (Some eqs)
and solve_unsolved env i p eqs =
  assert (not (Ident.rigid i));
  let flex_flex, to_handle = split_flex_flex env i p [] [] eqs.flex_flex in
  let solved_flex =
    Ident.Map.add i p (Ident.Map.map (Path.subst [(i, p)]) eqs.solved_flex)
  in
  let rigid_heads, to_handle =
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
      eqs.rigid_heads (Ident.Map.empty, to_handle)
  in
  let type_constraints = eqs.type_constraints in (* TODO : inject equality in type_constraints *)
  List.fold_left
    (fun eqs (k, p1, p2) -> add_path_eq env k p1 p2 eqs)
    (Some {flex_flex; solved_flex; rigid_heads; type_constraints})
    to_handle
and add_path_type_eq env p tyl ty eqs =
  if tyl = [] then
    match Types.get_desc ty with
    | Tconstr (p2, [], _) -> add_path_eq env Type p p2 eqs
    | _ ->
      Option.bind eqs (add_pt_normalizing env p tyl ty)
  else
      Option.bind eqs (add_pt_normalizing env p tyl ty)
and add_pt_normalizing env p tyl ty eqs =
  begin match Types.get_desc ty with Tconstr (_, [], _) -> assert false | _ -> () end;
  let p = Path.subst_map eqs.solved_flex p in
  match tyl with
  | [] ->
    begin
      match normalize_type_path env p with
      | PM_Path p ->
        add_pt_normalized env p [] ty eqs
      | PM_Manifest ty_of_path ->
        add_type_type_eq env ty_of_path ty eqs
    end
  | _ ->
    let p = Env.normalize_type_path (Some Location.none) env p in
    add_pt_normalized env p tyl ty eqs
and add_pt_normalized env p tyl ty eqs =
  let flex_ids = Path.get_flexs p in
  if flex_ids = [] then
    if tyl = [] then
      None
    else
      add_type_type_eq env
        (Btype.newgenty (Tconstr (p, tyl, ref Types.Mnil))) ty eqs
  else
  let add_one eqs i =
    let els =
      match Ident.Map.find i eqs.type_constraints with
      | els -> els
      | exception Not_found -> []
    in
    let type_constraints =
        Ident.Map.add i ((p, tyl, ty) :: els) eqs.type_constraints
    in
    { eqs with type_constraints }
  in Some (List.fold_left add_one eqs flex_ids)
and add_type_type_eq env ty1 ty2 eqs =
  if !incompatible env ty1 ty2 then
    None
  else begin
    Format.eprintf "ForgotAdd : %a = %a\n"
      Rawprinttyp.type_expr ty1
      Rawprinttyp.type_expr ty2;
    Some eqs
  end

let is_empty eqs =
  eqs.flex_flex = []
  && Ident.Map.is_empty eqs.rigid_heads
  && Ident.Map.is_empty eqs.solved_flex
  && Ident.Map.is_empty eqs.type_constraints

let solve_opt env k i p = function
  | None -> None
  | Some eqs -> solve env k i p eqs

let merge env eqs1 eqs2 =
  (* assert (Ident.Map.is_empty eqs1.solved_flex); *)
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
      (fun eqs (k, p1, p2) -> add_path_eq env k p1.path p2.path eqs)
      (Some eqs1) eqs2.flex_flex
  in
  let eqs =
    Ident.Map.fold
      (fun _ pl eqs ->
          List.fold_left
            (fun eqs p ->
                add_path_eq env p.eq_kind p.pp_rigid.path p.pp_flex.path eqs)
            eqs pl)
      eqs2.rigid_heads
      eqs
  in Ident.Map.fold (solve_opt env Module) eqs2.solved_flex eqs

let merge env eqs1 eqs2 =
  match eqs1, eqs2 with
  | None, _ | _, None -> None
  | Some eqs1, Some eqs2 ->
    if is_empty eqs1 then Some eqs2 else begin
      if is_empty eqs2 then Some eqs1 else begin
        if Ident.Map.is_empty eqs1.solved_flex then
          merge env eqs1 eqs2
        else
          merge env eqs2 eqs1
      end
    end

let is_empty = function Some eqs -> is_empty eqs | None -> false

let has_error_type_constraints env eqs =
  let rec has_contra p ty = function
    | [] -> false
    | (p2, [], ty2) :: tl ->
      begin
        match normalize_type_path env (Path.subst_map eqs.solved_flex p2) with
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
    | (p, [], ty) :: tl ->
      begin
        match normalize_type_path env (Path.subst_map eqs.solved_flex p) with
        | PM_Path p ->
          !incompatible env (Btype.newgenty (Tconstr (p, [], ref Types.Mnil))) ty || has_contra p ty tl
        | PM_Manifest ty' -> !incompatible env ty ty'
      end || has_error_one tl
    | _ :: tl -> has_error_one tl
  in
  Ident.Map.exists (fun _ l -> has_error_one l) eqs.type_constraints

let has_error env = function
  | None -> true
  | Some eqs -> has_error_type_constraints env eqs

let generalize _ cstrs =
  assert (is_empty cstrs);
  cstrs
