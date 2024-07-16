(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*  Xavier Leroy and Jerome Vouillon, projet Cristal, INRIA Rocquencourt  *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Basic operations on core types *)

open Types


(**** Sets, maps and hashtables of types ****)

let wrap_repr f ty = f (Transient_expr.repr ty)
let wrap_type_expr f tty = f (Transient_expr.type_expr tty)
module TransientTypeSet = Set.Make(TransientTypeOps)
module TypeSet = struct
  include TransientTypeSet
  let add = wrap_repr add
  let mem = wrap_repr mem
  let singleton = wrap_repr singleton
  let exists p = TransientTypeSet.exists (wrap_type_expr p)
  let elements set =
    List.map Transient_expr.type_expr (TransientTypeSet.elements set)
end


(**** Type level management ****)

let generic_level = Ident.highest_scope
let lowest_level = Ident.lowest_scope

let type_origin decl =
  match decl.type_kind with
  | Type_abstract origin -> origin
  | Type_variant _ | Type_record _ | Type_open -> Definition

let type_kind_is_abstract decl =
  match decl.type_kind with Type_abstract _ -> true | _ -> false

let is_fixed row = match row_fixed row with
  | None -> false
  | Some _ -> true

let static_row row =
  row_closed row &&
  List.for_all
    (fun (_,f) -> match row_field_repr f with Reither _ -> false | _ -> true)
    (row_fields row)

let row_of_type t =
  match get_desc t with
    Tobject(t,_) ->
      let rec get_row t =
        match get_desc t with
          Tfield(_,_,_,t) -> get_row t
        | _ -> t
      in get_row t
  | Tvariant row ->
      row_more row
  | _ ->
      t


(**** Check some types ****)

let is_Tvar ty = match get_desc ty with Tvar _ -> true | _ -> false
let is_Tunivar ty = match get_desc ty with Tunivar _ -> true | _ -> false
let is_Tconstr ty = match get_desc ty with Tconstr _ -> true | _ -> false
let is_poly_Tpoly ty =
  match get_desc ty with Tpoly (_, _ :: _) -> true | _ -> false
let label_is_poly lbl = is_poly_Tpoly lbl.lbl_arg

let dummy_method = "*dummy method*"

(**** Utilities for fixed row private types ****)

let has_constr_row t =
  not (is_Tconstr t) && is_Tconstr (row_of_type t)

let is_row_name s =
  let l = String.length s in
  (* PR#10661: when l=4 and s is "#row", this is not a row name
     but the valid #-type name of a class named "row". *)
  l > 4 && String.sub s (l-4) 4 = "#row"

let is_constr_row ~allow_ident t =
  match get_desc t with
    Tconstr (Path.Pident id, _, _) when allow_ident ->
      is_row_name (Ident.name id)
  | Tconstr (Path.Pdot (_, s), _, _) -> is_row_name s
  | _ -> false

(* TODO: where should this really be *)
(* Set row_name in Env, cf. GPR#1204/1329 *)
let set_static_row_name decl path =
  match decl.type_manifest with
    None -> ()
  | Some ty ->
      match get_desc ty with
        Tvariant row when static_row row ->
          let row =
            set_row_name row (Some (path, decl.type_params)) in
          set_type_desc ty (Tvariant row)
      | _ -> ()

(**** Type information getter ****)

let cstr_type_path cstr =
  match get_desc cstr.cstr_res with
  | Tconstr (p, _, _) -> p
  | _ -> assert false

                  (**********************************)
                  (*  Utilities for type traversal  *)
                  (**********************************)

let fold_row f init row =
  let result =
    List.fold_left
      (fun init (_, fi) ->
         match row_field_repr fi with
         | Rpresent(Some ty) -> f init ty
         | Reither(_, tl, _) -> List.fold_left f init tl
         | _ -> init)
      init
      (row_fields row)
  in
  match get_desc (row_more row) with
  | Tvar _ | Tunivar _ | Tsubst _ | Tconstr _ | Tnil ->
    begin match
      Option.map (fun (_,l) -> List.fold_left f result l) (row_name row)
    with
    | None -> result
    | Some result -> result
    end
  | _ -> assert false

let iter_row f row =
  fold_row (fun () v -> f v) () row

let fold_type_expr ?(allow_tsubst=false) f init ty =
  match get_desc ty with
    Tvar _              -> init
  | Tarrow (_, ty1, ty2, _) ->
      let result = f init ty1 in
      f result ty2
  | Ttuple l            -> List.fold_left f init l
  | Tconstr (_, l, _)   -> List.fold_left f init l
  | Tobject(ty, {contents = Some (_, p)}) ->
      let result = f init ty in
      List.fold_left f result p
  | Tobject (ty, _)     -> f init ty
  | Tvariant row        ->
      let result = fold_row f init row in
      f result (row_more row)
  | Tfield (_, _, ty1, ty2) ->
      let result = f init ty1 in
      f result ty2
  | Tnil                -> init
  | Tlink _ -> assert false
  | Tsubst _    ->
      assert allow_tsubst; init
  | Tunivar _           -> init
  | Tpoly (ty, tyl)     ->
    let result = f init ty in
    List.fold_left f result tyl
  | Tpackage (_, fl)  ->
    List.fold_left (fun result (_n, ty) -> f result ty) init fl
  | Tfunctor (_, _, (_, Cfp_module (_, fl)), ty) ->
      let res = List.fold_left (fun result (_n, ty) -> f result ty) init fl in
      f res ty
  | Tfunctor (_, _, _, ty) ->
      f init ty

let iter_type_expr ?(allow_tsubst=false) f ty =
  fold_type_expr ~allow_tsubst (fun () v -> f v) () ty


                  (**********************************)
                  (*  Utilities for copying         *)
                  (**********************************)

let copy_row f fixed row keep more =
  let Row {fields = orig_fields; fixed = orig_fixed; closed; name = orig_name} =
    row_repr row in
  let fields = List.map
      (fun (l, fi) -> l,
        match row_field_repr fi with
        | Rpresent oty -> rf_present (Option.map f oty)
        | Reither(c, tl, m) ->
            let use_ext_of = if keep then Some fi else None in
            let m = if is_fixed row then fixed else m in
            let tl = List.map f tl in
            rf_either tl ?use_ext_of ~no_arg:c ~matched:m
        | Rabsent -> rf_absent)
      orig_fields in
  let name =
    match orig_name with
    | None -> None
    | Some (path, tl) -> Some (path, List.map f tl) in
  let fixed = if fixed then orig_fixed else None in
  create_row ~fields ~more ~fixed ~closed ~name

let copy_commu c = if is_commu_ok c then commu_ok else commu_var ()

let rec copy_type_desc ?(keep_names=false) f = function
    Tvar _ as ty        -> if keep_names then ty else Tvar None
  | Tarrow (p, ty1, ty2, c)-> Tarrow (p, f ty1, f ty2, copy_commu c)
  | Ttuple l            -> Ttuple (List.map f l)
  | Tconstr (p, l, _)   -> Tconstr (p, List.map f l, ref Mnil)
  | Tobject(ty, {contents = Some (p, tl)})
                        -> Tobject (f ty, ref (Some(p, List.map f tl)))
  | Tobject (ty, _)     -> Tobject (f ty, ref None)
  | Tvariant _          -> assert false (* too ambiguous *)
  | Tfield (p, k, ty1, ty2) ->
      Tfield (p, field_kind_internal_repr k, f ty1, f ty2)
      (* the kind is kept shared, with indirections removed for performance *)
  | Tnil                -> Tnil
  | Tlink ty            -> copy_type_desc f (get_desc ty)
  | Tsubst _            -> assert false
  | Tunivar _ as ty     -> ty (* always keep the name *)
  | Tpoly (ty, tyl)     ->
      let tyl = List.map f tyl in
      Tpoly (f ty, tyl)
  | Tpackage (p, fl)  -> Tpackage (p, List.map (fun (n, ty) -> (n, f ty)) fl)
  | Tfunctor _ ->
      (* doing this would break unicity of uscoped binding in Tfunctor *)
      assert false

(* TODO: rename to [module Copy_scope] *)
module For_copy : sig
  type copy_scope

  val redirect_desc: copy_scope -> type_expr -> type_desc -> unit

  val with_scope: (copy_scope -> 'a) -> 'a
end = struct
  type copy_scope = {
    mutable saved_desc : (transient_expr * type_desc) list;
    (* Save association of generic nodes with their description. *)
  }

  let redirect_desc copy_scope ty desc =
    let ty = Transient_expr.repr ty in
    copy_scope.saved_desc <- (ty, ty.desc) :: copy_scope.saved_desc;
    Transient_expr.set_desc ty desc

  (* Restore type descriptions. *)
  let cleanup { saved_desc; _ } =
    List.iter (fun (ty, desc) -> Transient_expr.set_desc ty desc) saved_desc

  let with_scope f =
    let scope = { saved_desc = [] } in
    let res = f scope in
    cleanup scope;
    res
end

(* Predef of safe operations of type definitions *)

let newgenty desc =
  let ty = proto_newty3 ~level:generic_level
                        ~scope:Ident.lowest_scope desc in
  Transient_expr.type_expr ty

let newgenvar ?name () = newgenty (Tvar name)

let newgenstub ~scope  =
  let ty = proto_newty3 ~level:generic_level
                        ~scope (Tvar None) in
  Transient_expr.type_expr ty
