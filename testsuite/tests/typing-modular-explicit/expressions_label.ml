(* TEST
 expect;
*)

[@@@ocaml.warning "-5"]

(* Here the coercion requires computation and should? be forbidden *)
let try_coerce2 (f : x:int -> y:int -> int) = (f : (y:int -> x:int -> int))

[%%expect{|
Line 4, characters 47-48:
4 | let try_coerce2 (f : x:int -> y:int -> int) = (f : (y:int -> x:int -> int))
                                                   ^
Error: This expression has type "x:int -> y:int -> int"
       but an expression was expected of type "y:int -> x:int -> int"
|}]

(** Tests about unannoted applications *)
(* TODO : look at inference for labelled argument, similar patterns could be used
   An idea would be to allow inference in a similar pattern as label inference.
   This would lead in many cases to ill types being infered however the user could
   still correct this by adding more annotations to allow more general types to
   be infered.
*)

(* should fail because can't infer the type of f *)
let apply f ~t:int (x : int) : int = f ~t x

[%%expect{|
Line 10, characters 40-41:
10 | let apply f ~t:int (x : int) : int = f ~t x
                                             ^
Error: Unbound value "t"
|}]

(* ({T : Typ} -> T.t -> T.t -> T.t) -> {T : Typ} -> T.t -> T.t -> T.t *)
let apply_with_annot f ~t x =
  let _g : t:'b -> 'b -> 'b = f in
  f ~t x

let merge_no_mod (x : 'a) (y : 'a) = x

[%%expect{|
val apply_with_annot : (t:'b -> 'b -> 'b) -> t:'b -> 'b -> 'b = <fun>
val merge_no_mod : 'a -> 'a -> 'a = <fun>
|}]

(* The two next tests needs to be equivalent ! *)

(* should fail because `g` is not fully annotated ? *)
let apply_small_annot1 (f : t:'a -> 'a -> 'a) g ~t x =
  let r = g ~t x in (* g : {T : Typ} -> 'a -> 'b *)
  let _ = merge_no_mod f g in (* error : `{T : Typ} -> T.t -> T.t` and `{T : Typ} -> 'a -> 'b)` are not compatible *)
  (* because `T.t` and `'a` have incompatible scopes *)
  r

(* ({T : Typ} -> T.t -> T.t) -> ({T : Typ} -> T.t -> T.t) -> {T : Typ} -> T.t -> T.t *)
let apply_small_annot2 (f : t:'a -> 'a -> 'a) g ~t x =
  let _ = merge_no_mod f g in
  g ~t x

(* same error as `apply_small_annot1` *)
let apply_small_annot g ~t x : t:'a -> 'a -> 'a =
  let _ = g ~t x in
  g

[%%expect{|
val apply_small_annot1 :
  (t:'a -> 'a -> 'a) -> (t:'a -> 'a -> 'a) -> t:'a -> 'a -> 'a = <fun>
val apply_small_annot2 :
  (t:'a -> 'a -> 'a) -> (t:'a -> 'a -> 'a) -> t:'a -> 'a -> 'a = <fun>
val apply_small_annot : (t:'a -> 'a -> 'a) -> t:'a -> 'a -> t:'a -> 'a -> 'a =
  <fun>
|}]


let test1 (g : x:int -> _) = g ~x:1 ~y:2 + g ~y:3 ~x:4

[%%expect{|
val test1 : (x:int -> y:int -> int) -> int = <fun>
|}]

let test1 g = g ~x:1 ~y:2 + g ~y:3 ~x:4

[%%expect{|
Line 1, characters 28-29:
1 | let test1 g = g ~x:1 ~y:2 + g ~y:3 ~x:4
                                ^
Error: This function is applied to arguments
       in an order different from other calls.
       This is only allowed when the real type is known.
|}]

let test2 g =
  let a = g ~x:1 ~y:2 in
  a + g ~y:3 ~x:4

[%%expect{|
Line 3, characters 6-7:
3 |   a + g ~y:3 ~x:4
          ^
Error: This function is applied to arguments
       in an order different from other calls.
       This is only allowed when the real type is known.
|}]

(* Next tests are doing funny things *)

let require_args_applied g = g ~x:1 ~y:2
let require_args_annotated (g : x:int -> y:int -> 'a) : 'a = g ~x:1 ~y:2

[%%expect{|
val require_args_applied : (x:int -> y:int -> 'a) -> 'a = <fun>
val require_args_annotated : (x:int -> y:int -> 'a) -> 'a = <fun>
|}]

let test3 g =
  let a = require_args_applied g in
  a + g ~y:3 ~x:4

[%%expect{|
Line 3, characters 6-7:
3 |   a + g ~y:3 ~x:4
          ^
Error: This function is applied to arguments
       in an order different from other calls.
       This is only allowed when the real type is known.
|}]

let test4 g =
  let a = require_args_annotated g in
  a + g ~y:3 ~x:4

[%%expect{|
val test4 : (x:int -> y:int -> int) -> int = <fun>
|}, Principal{|
Line 3, characters 16-17:
3 |   a + g ~y:3 ~x:4
                    ^
Warning 18 [not-principal]: commuting this argument is not principal.

val test4 : (x:int -> y:int -> int) -> int = <fun>
|}]


let test5 g =
  let _ : x:int -> y:int -> int = g in
  g ~x:1 ~y:2 + g ~y:3 ~x:4

[%%expect{|
val test5 : (x:int -> y:int -> int) -> int = <fun>
|}, Principal{|
Line 3, characters 26-27:
3 |   g ~x:1 ~y:2 + g ~y:3 ~x:4
                              ^
Warning 18 [not-principal]: commuting this argument is not principal.

val test5 : (x:int -> y:int -> int) -> int = <fun>
|}]

let test6 g =
  require_args_applied g + g ~y:3 ~x:4

[%%expect{|
Line 2, characters 27-28:
2 |   require_args_applied g + g ~y:3 ~x:4
                               ^
Error: This function is applied to arguments
       in an order different from other calls.
       This is only allowed when the real type is known.
|}]

let test7 g =
  require_args_annotated g + g ~y:3 ~x:4

[%%expect{|
val test7 : (x:int -> y:int -> int) -> int = <fun>
|}, Principal{|
Line 2, characters 39-40:
2 |   require_args_annotated g + g ~y:3 ~x:4
                                           ^
Warning 18 [not-principal]: commuting this argument is not principal.

val test7 : (x:int -> y:int -> int) -> int = <fun>
|}]

let test8 g =
  let a = g ~y:3 ~x:4 in
  require_args_annotated g + a

[%%expect{|
Line 3, characters 25-26:
3 |   require_args_annotated g + a
                             ^
Error: This expression has type "y:int -> x:int -> 'a"
       but an expression was expected of type "x:int -> y:int -> 'b"
|}]
