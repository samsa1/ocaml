(* TEST
   expect;
*)

module type T = sig
  type t
end

module type T2 = sig
  type t
end

module type Add = sig
  type t
  val add : t -> t -> t
end

[%%expect{|
module type T = sig type t end
module type T2 = sig type t end
module type Add = sig type t val add : t -> t -> t end
|}]

type t1 =
  | A1 of (int -> int)
  | B1 of ({M : T} -> M.t -> M.t)

let f = function
  | A1 f -> f 1
  | B1 f -> f {Int} 2

[%%expect{|
type t1 = A1 of (int -> int) | B1 of ({M : T} -> M.t -> M.t)
val f : t1 -> Int.t = <fun>
|}]

type _ t2 =
  | A : (int -> int) t2
  | B : ({M : T} -> M.t -> M.t) t2
  | C : ({M : T2} -> M.t -> M.t) t2
  | D : ({M : Add} -> M.t -> M.t) t2

[%%expect{|
type _ t2 =
    A : (int -> int) t2
  | B : ({M : T} -> M.t -> M.t) t2
  | C : ({M : T2} -> M.t -> M.t) t2
  | D : ({M : Add} -> M.t -> M.t) t2
|}]

(* matching specification *)

let f (type a) (x : a) (el : a t2) =
  match el, x with
  | A, f -> f 1
  | B, f -> f {Int} 2
  | C, f -> f {Int} 3
  | D, f -> f {Int} 4

[%%expect{|
val f : 'a -> 'a t2 -> int = <fun>
|}, Principal{|
Line 3, characters 12-15:
3 |   | A, f -> f 1
                ^^^
Error: This expression has type "int" but an expression was expected of type "'a"
       This instance of "int" is ambiguous:
       it would escape the scope of its equation
|}]

let f (type a) (x : a) (el : ({N : T} -> a) t2) =
  match el, x with
  | B, f -> f
  | C, f -> f

[%%expect{|
Lines 2-4, characters 2-13:
2 | ..match el, x with
3 |   | B, f -> f
4 |   | C, f -> f
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
Here is an example of a case that is not matched:
(D, _)

val f : 'a -> ({N : T} -> 'a) t2 -> 'a = <fun>
|}]

let f (type a) (x : a) (el : ({N : Add} -> a) t2) =
  match el, x with
  | D, f -> f

[%%expect{|
Lines 2-3, characters 2-13:
2 | ..match el, x with
3 |   | D, f -> f
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
Here is an example of a case that is not matched:
(B, _)

val f : 'a -> ({N : Add} -> 'a) t2 -> 'a = <fun>
|}]

(* escape errors *)

