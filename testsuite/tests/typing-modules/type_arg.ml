(* TEST
 expect;
*)

module type F = functor (type a) -> sig
  val default : a
end

module List (type a) = struct
  type t = a list
end

module List2 = functor (type a) -> struct
  type t = (a * a) list
end

[%%expect{|
module type F = functor (type a) -> sig val default : a end
module List : functor (type a) -> sig type t = a list end
module List2 : functor (type a) -> sig type t = (a * a) list end
|}]

module IntList = List(type int)

module SumList = List(type [`A | `B])

[%%expect{|
module IntList : sig type t = int list end
module SumList : sig type t = [ `A | `B ] list end
|}]

(* Test all cases of wrong applications of modules *)

module Err1 = List(Int)

[%%expect{|
Line 1, characters 14-23:
1 | module Err1 = List(Int)
                  ^^^^^^^^^
Error: The functor was expected to be generative at this position
|}]

module Err2 = List()

[%%expect{|
Line 1, characters 14-20:
1 | module Err2 = List()
                  ^^^^^^
Error: The functor was expected to be applicative at this position
|}]

module type T = sig
  type t
end

module Id (X : T) = X

[%%expect{|
module type T = sig type t end
module Id : functor (X : T) -> sig type t = X.t end
|}]

module Err3 = Id(type int)

(* TODO : correct this error message *)
[%%expect{|
Line 1, characters 14-26:
1 | module Err3 = Id(type int)
                  ^^^^^^^^^^^^
Error: The functor was expected to be generative at this position
|}]

module G () = struct end

module Err4 = G(type int)

[%%expect{|
module G : functor () -> sig end
Line 3, characters 14-15:
3 | module Err4 = G(type int)
                  ^
Error: This is a generative functor. It can only be applied to "()"
|}]

(* Test coercions *)

module Swaping : functor (type a) (type b) -> sig
    type t = a
    type s = b
end = functor (type b) (type a) -> struct
    type t = b
    type s = a
end

[%%expect{|
module Swaping : functor (type a) (type b) -> sig type t = a type s = b end
|}]

module Err5 : functor (type t) -> sig type nonrec t = t end = Id

[%%expect{|
Line 1, characters 62-64:
1 | module Err5 : functor (type t) -> sig type nonrec t = t end = Id
                                                                  ^^
Error: Signature mismatch:
       Modules do not match:
         functor (X : T) -> ...
       is not included in
         functor (type t) -> ...
       The functor was expected to be generative at this position
|}]

let f1 (x : List(type int).t) : List(type int).t = x

module M = List(type int)

let f2 (x : M.t) : List(type int).t = x

[%%expect{|
val f1 : List(type int).t -> List(type int).t = <fun>
module M : sig type t = int list end
val f2 : M.t -> List(type int).t = <fun>
|}]

let f_fail (x : List(type int).t) : List(type float).t = x

[%%expect{|
Line 1, characters 57-58:
1 | let f_fail (x : List(type int).t) : List(type float).t = x
                                                             ^
Error: This expression has type "List(type int).t" = "int list"
       but an expression was expected of type "List(type float).t" = "float list"
       Type "int" is not compatible with type "float"
|}]
