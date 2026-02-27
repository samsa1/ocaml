(* TEST
 expect;
*)

type[@unboxed] 'a foo = { foo : 'b } constraint 'a = 'b * 'c
[%%expect{|
type 'a foo = { foo : 'b; } constraint 'a = 'b * 'c [@@unboxed]
|}];;

let bar : 'c. (unit * 'c) foo = { foo = () }
[%%expect{|
Uncaught exception: Ctype.Cannot_apply

|}];;

