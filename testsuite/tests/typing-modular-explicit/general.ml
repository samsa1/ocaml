(* TEST
  expect;
*)

module type Typ = sig type t end

module type Add = sig type t val add : t -> t -> t end

let id {T : Typ} (x : T.t) = x

let id2 : {T : Typ} -> T.t -> T.t =
  fun {A : Typ} (x : A.t) -> x

[%%expect{|
module type Typ = sig type t end
module type Add = sig type t val add : t -> t -> t end
val id : {T : Typ} -> T.t -> T.t = <fun>
val id2 : {T : Typ} -> T.t -> T.t = <fun>
|}]


let f x y = (id {Int} x, id {Bool} y)

[%%expect{|
val f : Int.t -> Bool.t -> Int.t * Bool.t = <fun>
|}]

let merge {T : Typ} x y = (id {T} x, id {T} y)

[%%expect{|
val merge : {T : Typ} -> T.t -> T.t -> T.t * T.t = <fun>
|}]



let alpha_equiv (f : {A : Add} -> A.t -> A.t) : {T : Add} -> T.t -> T.t = f

[%%expect{|
val alpha_equiv : ({A : Add} -> A.t -> A.t) -> {T : Add} -> T.t -> T.t =
  <fun>
|}]


(* Typing rules make sense only if module argument are
   a path (module names, projections and applications) *)
let x_from_struct = id {struct type t = int end} 3

[%%expect{|
Line 1, characters 24-47:
1 | let x_from_struct = id {struct type t = int end} 3
                            ^^^^^^^^^^^^^^^^^^^^^^^
Error: Cannot infer path of module for functor.
|}]


module type Map = sig
  type _ t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

let map {M : Map} f x = M.map f x

[%%expect{|
module type Map = sig type _ t val map : ('a -> 'b) -> 'a t -> 'b t end
val map : {M : Map} -> ('a -> 'b) -> 'a M.t -> 'b M.t = <fun>
|}]


let s_list = map {List} string_of_int [3; 1; 4]

[%%expect{|
val s_list : string List.t = List.(::) ("3", ["1"; "4"])
|}]


module MapCombin (M1 : Map) (M2 : Map) = struct
  type 'a t = 'a M1.t M2.t
  let map f = map {M2} (map {M1} f)
end

let s_list_array = map {MapCombin(List)(Array)} string_of_int [|[3; 2]; [2]; []|]

[%%expect{|
module MapCombin :
  functor (M1 : Map) (M2 : Map) ->
    sig
      type 'a t = 'a M1.t M2.t
      val map : ('a -> 'b) -> 'a M1.t M2.t -> 'b M1.t M2.t
    end
val s_list_array : string MapCombin(List)(Array).t =
  [|List.(::) ("3", ["2"]); List.(::) ("2", []); List.[]|]
|}]


let s_list_arrayb =
    map {MapCombin(struct type 'a t = 'a list let map = List.map end)(Array)}
    [|[3; 2]; [2]; []|]

[%%expect{|
Line 2, characters 9-76:
2 |     map {MapCombin(struct type 'a t = 'a list let map = List.map end)(Array)}
             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Cannot infer path of module for functor.
|}]


module type AddSub = sig
  type t
  val add : t -> t -> t
  val sub : t -> t -> t
end

module type SubAdd = sig
  type t
  val sub : t -> t -> t
  val add : t -> t -> t
end

[%%expect{|
module type AddSub =
  sig type t val add : t -> t -> t val sub : t -> t -> t end
module type SubAdd =
  sig type t val sub : t -> t -> t val add : t -> t -> t end
|}]


let try_coerce (f : {A : Add} -> A.t -> A.t) : {T : Typ} -> T.t -> T.t = f

[%%expect{|
Line 1, characters 73-74:
1 | let try_coerce (f : {A : Add} -> A.t -> A.t) : {T : Typ} -> T.t -> T.t = f
                                                                             ^
Error: This expression has type "{A : Add} -> A.t -> A.t"
       but an expression was expected of type "{T : Typ} -> T.t -> T.t"
|}]


(* Here the coercion requires computation and should? be forbidden *)
let try_coerce2 (f : {A : AddSub} -> A.t -> A.t) = (f :> ({T : SubAdd} -> T.t -> T.t))

[%%expect{|
Line 1, characters 51-86:
1 | let try_coerce2 (f : {A : AddSub} -> A.t -> A.t) = (f :> ({T : SubAdd} -> T.t -> T.t))
                                                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Type "{A : AddSub} -> A.t -> A.t" is not a subtype of
         "{T : SubAdd} -> T.t -> T.t"
|}]


(* Here the coercion does not require any computation and thus could be allowed *)
let try_coerce3 (f : {A : Add} -> A.t -> A.t) = (f :> {T : Typ} -> T.t -> T.t)

[%%expect{|
Line 1, characters 48-78:
1 | let try_coerce3 (f : {A : Add} -> A.t -> A.t) = (f :> {T : Typ} -> T.t -> T.t)
                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Type "{A : Add} -> A.t -> A.t" is not a subtype of
         "{T : Typ} -> T.t -> T.t"
|}]


(** Tests about unannoted applications *)

let apply f {T : Typ} (x : T.t) : T.t = f {T} x

[%%expect{|
Line 3, characters 43-44:
3 | let apply f {T : Typ} (x : T.t) : T.t = f {T} x
                                               ^
Error: Cannot infer signature of functor.
|}]

let apply_with_annot f {T : Typ} (x : T.t) : T.t =
  let _g : {T : Typ} -> T.t -> T.t = f in
  f {T} x

(* (type a) -> a -> a -> a *)
let merge_no_mod (type a) (x : a) (y : a) = x

[%%expect{|
val apply_with_annot : ({T : Typ} -> T.t -> T.t) -> {T : Typ} -> T.t -> T.t =
  <fun>
val merge_no_mod : 'a -> 'a -> 'a = <fun>
|}]


let apply_small_annot1 (f : {T : Typ} -> T.t -> T.t) g {T : Typ} x =
  let r = g {T} x in
  let _ = merge_no_mod f g in
  r

[%%expect{|
Line 2, characters 13-14:
2 |   let r = g {T} x in
                 ^
Error: Cannot infer signature of functor.
|}]


let apply_small_annot2 (f : {T : Typ} -> T.t -> T.t) g {T : Typ} x =
  let _ = merge_no_mod f g in
  g {T} x

[%%expect{|
val apply_small_annot2 :
  ({T : Typ} -> T.t -> T.t) ->
  ({T : Typ} -> T.t -> T.t) -> {T : Typ} -> T.t -> T.t = <fun>
|}]


(* This is a syntax error *)
(* let id_bool_fail {B : module type of Bool} (x : B.t) = x *)

module type TBool = module type of Bool
let id_bool {B : TBool} (x : B.t) = x

[%%expect{|
module type TBool =
  sig
    type t = bool = false | true
    val not : bool -> bool
    external ( && ) : bool -> bool -> bool = "%sequand"
    external ( || ) : bool -> bool -> bool = "%sequor"
    val equal : bool -> bool -> bool
    val compare : bool -> bool -> int
    val to_int : bool -> int
    val to_float : bool -> float
    val to_string : bool -> string
    val seeded_hash : int -> bool -> int
    val hash : bool -> int
  end
val id_bool : {B : TBool} -> B.t -> B.t = <fun>
|}]


(** Escape errors **)

let r = ref None

let set {T : Typ} (x : T.t) =
  r := Some x

[%%expect{|
val r : '_weak1 option ref = {contents = None}
Line 6, characters 12-13:
6 |   r := Some x
                ^
Error: This expression has type "T.t" but an expression was expected of type
         "'weak1"
       The type constructor "T.t" would escape its scope
|}]


let f x {A : Add} (y : A.t) = A.add x y

[%%expect{|
Line 1, characters 36-37:
1 | let f x {A : Add} (y : A.t) = A.add x y
                                        ^
Error: This expression has type "'a" but an expression was expected of type "A.t"
       The type constructor "A.t" would escape its scope
|}]
