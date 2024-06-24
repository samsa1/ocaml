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

let apply_fcm = id_fcm (module Int) 11
let apply_fcm' = id_fcm (module struct type t = int end) 12
let apply_modexp = id_modexp {Int} 2
let apply_modimpl = id_modimpl ~t:{Int} 31
(* let apply_modimpl' = id_modimpl 32 *) (* Not implemented *)
let apply_modimpl2 = id_modimpl2 ?{Int} 41
(* let apply_modimpl2' = id_modimpl 42 *) (* Not implemented *)
let apply_fcm_t = id_fcm_t (module (type int)) 5
let apply_fcm_t' = id_fcm_t (module (type _)) 6
let apply_modexp_t  = id_modexp_t {type int} 7
let apply_modexp_t' = id_modexp_t {type _} 8
let apply_modimpl_t = id_modimpl_t ?{type int} 9
let apply_modimpl_t'  = id_modimpl_t 10

[%%expect{|
val apply_fcm : Int.t = 11
val apply_fcm' : int = 12
val apply_modexp : Int.t = 2
val apply_modimpl : Int.t = 31
val apply_modimpl2 : Int.t = 41
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
Uncaught exception: Failure("Modular implicits inference not implemented")

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

let seven_explicit2 = add {struct type t = int let add = Int.add end} 3 4

let seven_explicit3 = add {struct include Int end} 3 4

[%%expect{|
val seven_explicit2 : int = 7
val seven_explicit3 : int = 7
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
