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

type t = (Path.t * Types.type_expr list * Types.type_expr) list Ident.Map.t

let empty = Ident.Map.empty

let is_empty x = Ident.Map.is_empty x
let size x = Ident.Map.fold (fun _ el acc -> acc + List.length el) x 0

let type_expr_printer = ref (fun _ _ -> assert false)

let print_one fmt (p, tyl, ty) =
    Format_doc.fprintf fmt "%a(%a) => %a\n"
      Path.print p
      (Format_doc.pp_print_list !type_expr_printer) tyl
      !type_expr_printer ty

let print fmt constraints =
  Ident.Map.iter
    (fun i constraints ->
      Format_doc.fprintf fmt "\t%s[%d] =>\n\t@[<hov>%a@]"
        (Ident.name i)
        (List.length constraints)
        (Format_doc.pp_print_list print_one) constraints)
    constraints

let add p tyl ty constraints =
  let add_one constraints i =
    let els =
      match Ident.Map.find i constraints with
      | els -> els
      | exception Not_found -> []
    in
    Ident.Map.add i ((p, tyl, ty) :: els) constraints
  in
  List.fold_left add_one constraints (Path.get_flexs p)

let incompatible = ref (fun _ _ _ -> assert false)

let has_error env constraints =
  let rec has_contra p ty = function
    | [] -> false
    | (p2, [], ty2) :: tl when Path.same p p2 ->
      !incompatible env ty ty2 || has_contra p ty tl
    | _ :: tl -> has_contra p ty tl
  in
  let rec has_error_one = function
    | [] -> false
    | (p, [], ty) :: tl ->
      has_contra p ty tl || has_error_one tl
    | _ :: tl -> has_error_one tl
  in
  Ident.Map.exists (fun _ l -> has_error_one l) constraints

let merge a b =
  Ident.Map.merge
    (fun _i x y ->
      match x, y with
      | None, None -> None
      | Some x, None | None, Some x -> Some x
      | Some x, Some y -> Some (List.append x y))
    a b

let generalize _ cstrs =
  assert (is_empty cstrs);
  cstrs

let iter f constraints l =
  List.fold_left (fun constraints x -> merge constraints (f x)) constraints l

let iter2 f constraints l1 l2 =
  List.fold_left2
    (fun constraints x y -> merge constraints (f x y))
    constraints l1 l2
