(* TEST
  expect;
*)

module type T = sig type t end

let id_fcm (module M : T) (x : M.t) = x
let id_modexp {M : T} (x : M.t) = x
let id_modimpl ?t:{M : T} (x : M.t) = x
let id_modimpl2 ?{M : T} (x : M.t) = x
let id_fcm_t (module (type a)) (x : a) = x
let id_modexp_t {type a} (x : a) = x
let id_modimpl_t ?{type a} (x : a) = x

[%%expect{|
module type T = sig type t end
val id_fcm : (module M : T) -> M.t -> M.t = <fun>
val id_modexp : {M : T} -> M.t -> M.t = <fun>
val id_modimpl : ?t:{M : T} -> M.t -> M.t = <fun>
val id_modimpl2 : ?{M : T} -> M.t -> M.t = <fun>
val id_fcm_t : (module (type a)) -> a -> a = <fun>
val id_modexp_t : {type a} -> a -> a = <fun>
val id_modimpl_t : ?{type a} -> a -> a = <fun>
|}]

let apply_fcm = id_fcm (module Int) 1
let apply_modexp = id_modexp {Int} 2
let apply_modimpl = id_modimpl ~t:{Int} 3
let apply_modimpl2 = id_modimpl2 ?{Int} 3
(* let apply_modimpl' = id_modimpl 4 *) (* Not implemented *)
(* let apply_modimpl2' = id_modimpl 4 *) (* Not implemented *)
let apply_fcm_t = id_fcm_t (module (type int)) 5
let apply_fcm_t' = id_fcm_t (module (type _)) 6
let apply_modexp_t  = id_modexp_t {type int} 7
let apply_modexp_t' = id_modexp_t {type _} 8
let apply_modimpl_t = id_modimpl_t ?{type int} 9
let apply_modimpl_t'  = id_modimpl_t 10

[%%expect{|
val apply_fcm : Int.t = 1
val apply_modexp : Int.t = 2
val apply_modimpl : Int.t = 3
val apply_modimpl2 : Int.t = 3
val apply_fcm_t : int = 5
val apply_fcm_t' : int = 6
val apply_modexp_t : int = 7
val apply_modexp_t' : int = 8
val apply_modimpl_t : int = 9
val apply_modimpl_t' : int = 10
|}]

module type Add = sig type t val add : t -> t -> t end

let add {A : Add} (x : A.t) (y : A.t) = A.add x y

let add_lbl ~a:{A : Add} (x : A.t) (y : A.t) = A.add x y

let add_impl ?add:{A : Add} (x : A.t) (y : A.t) = A.add x y

[%%expect{|
module type Add = sig type t val add : t -> t -> t end
val add : {A : Add} -> A.t -> A.t -> A.t = <fun>
val add_lbl : a:{A : Add} -> A.t -> A.t -> A.t = <fun>
val add_impl : ?add:{A : Add} -> A.t -> A.t -> A.t = <fun>
|}]


(* Fails because modular implicit is not implemented *)

let seven = add_impl 3 4

[%%expect{|
Line 1, characters 12-20:
1 | let seven = add_impl 3 4
                ^^^^^^^^
Error: Inference of signature sig type t = int val add : t -> t -> t end
       failed as no solution was found.
|}]

(* Fails because argument was explicit *)
let seven_fail = add 3 4

[%%expect{|
Line 1, characters 17-20:
1 | let seven_fail = add 3 4
                     ^^^
Error: Applied an expression argument
       but expected a compact module argument.
|}]

let seven_explicit = add {Int} 3 4

[%%expect{|
val seven_explicit : Int.t = 7
|}]

(* Fails because argument was explicit *)
let seven_fail2 = add_lbl 3 4

[%%expect{|
Line 1, characters 18-25:
1 | let seven_fail2 = add_lbl 3 4
                      ^^^^^^^
Error: This expression has type "a:{A : Add} -> A.t -> A.t -> A.t"
       Received an expression argument. However, module arguments cannot be omitted.
|}]


let add_lbl_coerced = (add_lbl :> a:(module A : Add) -> A.t -> A.t -> A.t)

[%%expect{|
val add_lbl_coerced : a:(module A : Add) -> A.t -> A.t -> A.t = <fun>
|}]

let test_impl1 {A : Add} x y = add_impl x y
let test_impl2 {A : Add} {B : Add} (x : A.t) y = add_impl x y

[%%expect{|
val test_impl1 : {A : Add} -> A.t -> A.t -> A.t = <fun>
val test_impl2 : {A : Add} -> {B : Add} -> A.t -> A.t -> A.t = <fun>
|}]

let test_impl_fail1 {A : Add} {B : Add} x y = add_impl x y

[%%expect{|
Line 1, characters 46-54:
1 | let test_impl_fail1 {A : Add} {B : Add} x y = add_impl x y
                                                  ^^^^^^^^
Error: Inference of signature sig type t = 'a val add : t -> t -> t end
       failed as multiple solutions were found.
|}]

module type AddSub = sig
       type t
       val add: t -> t -> t
       val sub: t -> t -> t
end

let test_impl3 {AS : AddSub} (x : AS.t) y = add_impl x y

[%%expect{|
module type AddSub =
  sig type t val add : t -> t -> t val sub : t -> t -> t end
val test_impl3 : {AS : AddSub} -> AS.t -> AS.t -> AS.t = <fun>
|}]

module T1 = struct
       implicit module AInt = struct
              type t = int
              let add = ( + )
       end

       implicit module AFloat = struct
              type t = float
              let add = ( +. )
       end


       let seven = add_impl 3 4

       let seven_float = add_impl 5. 2.
end

[%%expect{|
module T1 :
  sig
    module AInt : sig type t = int val add : int -> int -> int end
    module AFloat : sig type t = float val add : float -> float -> float end
    val seven : int
    val seven_float : float
  end
|}]
