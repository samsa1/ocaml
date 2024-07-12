(* TEST
 expect;
*)

module type F = functor (type a) -> sig
  val default : a
end

module List (type a) = struct
  type t = a list
end

(* test alpha renaming *)
module List2 : functor (type b) -> sig
  type t = (b * b) list
end = functor (type a) -> struct
  type t = (a * a) list
end

[%%expect{|
module type F = functor (type a) -> sig val default : a end
module List : functor (type a) -> sig type t = a list end
module List2 : functor (type b) -> sig type t = (b * b) list end
|}]

(* Test valid applications *)

module IntList = List(type int)

module SumList = List(type [`A | `B])

[%%expect{|
module IntList : sig type t = int list end
module SumList : sig type t = [ `A | `B ] list end
|}]

(* Test all cases of wrong applications of modules for error messages *)

module Err1 = List(Int)

[%%expect{|
Line 1, characters 14-23:
1 | module Err1 = List(Int)
                  ^^^^^^^^^
Error: The functor expected a type argument at this position
|}]

module Err2 = List()

[%%expect{|
Line 1, characters 14-20:
1 | module Err2 = List()
                  ^^^^^^
Error: The functor expected a type argument at this position
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

[%%expect{|
Line 1, characters 14-26:
1 | module Err3 = Id(type int)
                  ^^^^^^^^^^^^
Error: The functor was expected to be applicative at this position
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

(* Test coercions between types and related errors messages *)

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
       The functor expected a type argument at this position
|}]

module type Typ = sig type t end

module Err6 : functor (T : Typ) -> sig
  type t = (T.t * T.t) list
end = functor (type a) -> struct
  type t = (a * a) list
end

[%%expect{|
module type Typ = sig type t end
Lines 5-7, characters 14-3:
5 | ..............(type a) -> struct
6 |   type t = (a * a) list
7 | end
Error: Signature mismatch:
       Modules do not match:
         functor (type a) -> ...
       is not included in
         functor (T : Typ) -> ...
       The functor was expected to be applicative at this position
|}]


(* Test about applicativity of type application to a module *)

let f1 (x : List(type int).t) : List(type int).t = x

module M = List(type int)

let f2 (x : M.t) : List(type int).t = x

[%%expect{|
val f1 : List(type int).t -> List(type int).t = <fun>
module M : sig type t = int list end
val f2 : M.t -> List(type int).t = <fun>
|}]

let f_fail1 (x : List(type int).t) : List(type float).t = x

[%%expect{|
Line 1, characters 58-59:
1 | let f_fail1 (x : List(type int).t) : List(type float).t = x
                                                              ^
Error: This expression has type "List(type int).t" = "int list"
       but an expression was expected of type "List(type float).t" = "float list"
       Type "int" is not compatible with type "float"
|}]

(* Test error message if the type is a parametric type *)
let f_fail2 (x : List(type list).t) = x

[%%expect{|
Line 1, characters 17-34:
1 | let f_fail2 (x : List(type list).t) = x
                     ^^^^^^^^^^^^^^^^^
Error: The type constructor list expects 1 argument(s)
|}]

(* Tests error messages of invalid application in paths *)

let fail_in_path (x : List(Int).t) = x

[%%expect{|
Line 1, characters 22-33:
1 | let fail_in_path (x : List(Int).t) = x
                          ^^^^^^^^^^^
Error: The functor expected a type argument at this position
|}]

module type Typ = sig type t end

module IdTyp (T : Typ) = T

let fail_in_path2 (x : IdTyp(type int).t) = x

[%%expect{|
module type Typ = sig type t end
module IdTyp : functor (T : Typ) -> sig type t = T.t end
Line 5, characters 23-40:
5 | let fail_in_path2 (x : IdTyp(type int).t) = x
                           ^^^^^^^^^^^^^^^^^
Error: The functor was expected to be applicative at this position
|}]


(** Check that type-functors receive the same checks as applicative functors
  All the following tests go by two : one with a module argument and one with
  a type argument to check that both work the same way
*)

(* Preliminaries *)

module Gen () : Typ = struct type t = int end

[%%expect{|
module Gen : functor () -> Typ
|}]


(* No unpacking of first-class module in applicative functors *)

module F1app (T : Typ) = struct
  let m = (module T : Typ)
  module M = (val m)
end

[%%expect{|
Line 3, characters 13-20:
3 |   module M = (val m)
                 ^^^^^^^
Error: This expression creates fresh types.
       It is not allowed inside applicative functors.
|}]

module F1typ (type a) = struct
  module T = struct type t = a end
  let m = (module T : Typ)
  module M = (val m)
end

[%%expect{|
Line 4, characters 13-20:
4 |   module M = (val m)
                 ^^^^^^^
Error: This expression creates fresh types.
       It is not allowed inside applicative functors.
|}]

module F2app (T : Typ) = Gen ()

[%%expect{|
Line 1, characters 25-31:
1 | module F2app (T : Typ) = Gen ()
                             ^^^^^^
Error: This expression creates fresh types.
       It is not allowed inside applicative functors.
|}]

module F2typ (type a) = Gen ()

[%%expect{|
Line 1, characters 24-30:
1 | module F2typ (type a) = Gen ()
                            ^^^^^^
Error: This expression creates fresh types.
       It is not allowed inside applicative functors.
|}]

(* Here we check that we don't have a scope escape of 'a inside the path. *)
let id (type a) (x : List(type a).t) = x

[%%expect{|
val id : 'a list -> 'a list = <fun>
|}]
