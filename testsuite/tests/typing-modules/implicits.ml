(* TEST
 flags = "-dno-locations -I ${ocamlsrcdir}/utils";
 expect;
*)


module type Show = sig
  type t
  val print : t -> unit
end

implicit module SInt = struct
  type t = int
  let print x = print_int x
end

implicit module SBool = struct
  type t = bool
  let print x = if x then print_string "true" else print_string "false"
end

[%%expect{|
module type Show = sig type t val print : t -> unit end
implicit module SInt : sig type t = int val print : int -> unit end
implicit module SBool : sig type t = bool val print : bool -> unit end
|}]

module SInt2 : Show with type t = int = _

[%%expect{|
Line 1, characters 13-41:
1 | module SInt2 : Show with type t = int = _
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SInt"

module SInt2 : sig type t = int val print : t -> unit end
|}]

implicit module SList (X : Show) = struct
  type t = X.t list

  let print l =
    let rec aux = function
      | [] -> print_char ']'
      | [x] -> X.print x; print_char ']'
      | hd :: tl ->
          X.print hd;
          print_string "; ";
          aux tl
    in print_char '['; aux l
end

[%%expect{|
implicit module SList :
  (X : Show) => sig type t = X.t list val print : X.t list -> unit end
|}]

module SIntL = (_ : Show with type t = int list)

module SIntLL : Show with type t = int list list = _

[%%expect{|
Line 1, characters 15-48:
1 | module SIntL = (_ : Show with type t = int list)
                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SList(SInt)"

module SIntL : sig type t = int list val print : t -> unit end
Line 3, characters 14-52:
3 | module SIntLL : Show with type t = int list list = _
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SList(SList(SInt))"

module SIntLL : sig type t = int list list val print : t -> unit end
|}]

(* No solution *)
module SFloat_fail : Show with type t = float = _

[%%expect{|
Line 1, characters 19-49:
1 | module SFloat_fail : Show with type t = float = _
                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Inference of signature sig type t = float val print : t -> unit end
       failed as no solution was found.
|}]

(* Shadowing *)

implicit module SInt : Show with type t = float = struct
  type t = float
  let print = print_float
end

module SFloat : Show with type t = float = _

[%%expect{|
implicit module SInt : sig type t = float val print : t -> unit end
Line 6, characters 14-44:
6 | module SFloat : Show with type t = float = _
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SInt"

module SFloat : sig type t = float val print : t -> unit end
|}]

module SInt_fail : Show with type t = int = _

[%%expect{|
Line 1, characters 17-45:
1 | module SInt_fail : Show with type t = int = _
                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Inference of signature sig type t = int val print : t -> unit end
       failed as no solution was found.
|}]

(* restore env after shadowing test above *)
implicit module SInt : Show with type t = int = SInt2

[%%expect{|
implicit module SInt : sig type t = int val print : t -> unit end
|}]

(* Multiple solutions *)
implicit module SBoolbis = SBool

module SBool_fail : Show with type t = bool = _

[%%expect{|
implicit module SBoolbis = SBool
Line 3, characters 18-47:
3 | module SBool_fail : Show with type t = bool = _
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SBoolbis"

module SBool_fail : sig type t = bool val print : t -> unit end
|}]

(* Multiple solution because generative *)

implicit module SFloat () : Show with type t = float = struct
  type t = float
  let print = print_float
end

module SFloat_fail : Show with type t = float = _

[%%expect{|
implicit module SFloat : () -> sig type t = float val print : t -> unit end
Line 6, characters 19-49:
6 | module SFloat_fail : Show with type t = float = _
                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Inference of signature sig type t = float val print : t -> unit end
       failed because inference could not make
       any more progress.
       Final state was :
       SFloat ?1.
?1 can be filled by "()" which is ambiguous with itself.

|}]

(* Ensure no recursive loop *)

module type T = sig val loop : unit end
implicit module LOOP (X : T) = struct let loop = () end

module Loop_fail : T = _

[%%expect{|
module type T = sig val loop : unit end
implicit module LOOP : (X : T) => sig val loop : unit end
Line 4, characters 17-24:
4 | module Loop_fail : T = _
                     ^^^^^^^
Error: Inference of signature T
       failed because inference could not make
       any more progress.
       Final state was :
       LOOP (?1).
?1 could be filled with a new recursive call to LOOP
       with no termination guaranty.

|}]

(* Infering a functor *)

module SListBis : (X : Show) -> Show with type t = X.t list = _

[%%expect{|
Line 1, characters 16-63:
1 | module SListBis : (X : Show) -> Show with type t = X.t list = _
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SList"

module SListBis :
  (X : Show) -> sig type t = X.t list val print : t -> unit end
|}]

(* Infering a functor using an application *)

implicit module SPair (A : Show) (B : Show)
  : Show with type t = A.t * B.t
  = struct
  type t = A.t * B.t
  let print (a, b) =
    print_string "("; A.print a;
    print_string ", "; B.print b;
    print_string ")"
end

module SIntXPair : (X : Show) -> Show with type t = int * X.t = _

[%%expect{|
implicit module SPair :
  (A : Show) (B : Show) => sig type t = A.t * B.t val print : t -> unit end
Line 11, characters 17-65:
11 | module SIntXPair : (X : Show) -> Show with type t = int * X.t = _
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SPair(SInt)"

module SIntXPair :
  (X : Show) -> sig type t = int * X.t val print : t -> unit end
|}]

(* Inference between functor arguments *)

module type SSol1 = sig val valid1 : unit end
module type SSol2 = sig val valid2 : unit end

module type S1 = sig type t1 end
module type S2 = sig type t2 end

implicit module F1Imp2 (X : S1) (Y : S2 with type t2 = X.t1) : SSol1 = struct
  let valid1 = ()
end

implicit module F2Imp1 (X : S2) (Y : S1 with type t1 = X.t2) : SSol2 = struct
  let valid2 = ()
end

implicit module M1 : S1 with type t1 = int = struct type t1 = int end

implicit module M2a : S2 with type t2 = int  = struct type t2 = int end
implicit module M2b : S2 with type t2 = bool = struct type t2 = bool end

[%%expect{|
module type SSol1 = sig val valid1 : unit end
module type SSol2 = sig val valid2 : unit end
module type S1 = sig type t1 end
module type S2 = sig type t2 end
implicit module F1Imp2 : (X : S1) (Y : sig type t2 = X.t1 end) => SSol1
implicit module F2Imp1 : (X : S2) (Y : sig type t1 = X.t2 end) => SSol2
implicit module M1 : sig type t1 = int end
implicit module M2a : sig type t2 = int end
implicit module M2b : sig type t2 = bool end
|}]

module ShouldSucceed1 : SSol1 = _

[%%expect{|
Line 1, characters 22-33:
1 | module ShouldSucceed1 : SSol1 = _
                          ^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "F1Imp2(M1)(M2a)"

module ShouldSucceed1 : SSol1
|}]

module ShouldSucceed2 : SSol2 = _

[%%expect{|
Line 1, characters 22-33:
1 | module ShouldSucceed2 : SSol2 = _
                          ^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "F2Imp1(M2a)(M1)"

module ShouldSucceed2 : SSol2
|}]

(* Test quality of error message *)

implicit module M2c : S2 with type t2 = int = struct type t2 = int end

module FailsWithAmbiguity : SSol2 = _

[%%expect{|
implicit module M2c : sig type t2 = int end
Line 3, characters 26-37:
3 | module FailsWithAmbiguity : SSol2 = _
                              ^^^^^^^^^^^
Error: Inference of signature SSol2
       failed because inference could not make
       any more progress.
       Final state was :
       F2Imp1 (?1) (M1).
?1 awaited an argument of signature  S2
                          It can be filled by either  M2c  or  M2a.

|}]

(* May have only one solution but not coherent *)

module type SSol3 = sig val valid3 : unit end
module type S3 = sig type t3 end

implicit module M3 : S3 = struct type t3 = bool end

implicit module F3 (X : S1) (Y : S3 with type t3 = X.t1) : SSol3 = struct
  let valid3 = ()
end

[%%expect{|
module type SSol3 = sig val valid3 : unit end
module type S3 = sig type t3 end
implicit module M3 : S3
implicit module F3 : (X : S1) (Y : sig type t3 = X.t1 end) => SSol3
|}]

module ShouldSucceed3 : SSol3 = _

[%%expect{|
Line 1, characters 22-33:
1 | module ShouldSucceed3 : SSol3 = _
                          ^^^^^^^^^^^
Error: Inference of signature SSol3
       failed as no solution was found.
|}]

(* Test containing inference of a functor *)

module type MShow = sig
  module M : Show
end

implicit module ApplyF (F : Show => Show) = struct
  module M = F(SInt)
end

[%%expect{|
module type MShow = sig module M : Show end
implicit module ApplyF :
  (F : Show => Show) =>
    sig module M : sig type t = F(SInt).t val print : t -> unit end end
|}]

module InferFunctor1_Sol : MShow with type M.t = int list = ApplyF(SList)

module InferFunctor1 : MShow with type M.t = int list = _

[%%expect{|
module InferFunctor1_Sol :
  sig module M : sig type t = int list val print : t -> unit end end
Line 3, characters 21-57:
3 | module InferFunctor1 : MShow with type M.t = int list = _
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "ApplyF(SList)"

module InferFunctor1 :
  sig module M : sig type t = int list val print : t -> unit end end
|}]

module InferFunctor2_Sol : MShow with type M.t = bool * int =
  ApplyF(SPair(SBool))

module InferFunctor2 : MShow with type M.t = bool * int = _

[%%expect{|
module InferFunctor2_Sol :
  sig module M : sig type t = bool * int val print : t -> unit end end
Line 4, characters 21-59:
4 | module InferFunctor2 : MShow with type M.t = bool * int = _
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "ApplyF(SPair(SBoolbis))"

module InferFunctor2 :
  sig module M : sig type t = bool * int val print : t -> unit end end
|}]

(* We remove functors from env to prevent collision later *)
implicit module SList : sig end = struct end
implicit module SFloat : sig end = struct end
implicit module SPair : sig end = struct end

[%%expect{|
implicit module SList : sig end
implicit module SFloat : sig end
implicit module SPair : sig end
|}]

(* Test signature inference *)

module M_infer_sig = struct
  type t = int
  implicit module Show = SInt
end

[%%expect{|
module M_infer_sig : sig type t = int implicit module Show = SInt end
|}]

(* and test the environnment was not flooded *)
module Test_No_Open : Show with type t = int = _

[%%expect{|
Line 1, characters 20-48:
1 | module Test_No_Open : Show with type t = int = _
                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SInt"

module Test_No_Open : sig type t = int val print : t -> unit end
|}]

(* Test signature comparison  *)

module M_with_sig1 : sig
  type t
  implicit module Show : Show with type t = t
end = struct
  type t = int
  implicit module Show = SInt
end

module M_with_sig2 : sig
  type t
  module Show : Show with type t = t
end = struct
  type t = int
  implicit module Show = SInt
end

module M_with_sig3 : sig
  type t
  implicit module Show : Show with type t = t
end = struct
  type t = int
  module Show = SInt
end

[%%expect{|
module M_with_sig1 :
  sig
    type t
    implicit module Show : sig type t = t/2 val print : t -> unit end
  end
module M_with_sig2 :
  sig type t module Show : sig type t = t/2 val print : t -> unit end end
module M_with_sig3 :
  sig
    type t
    implicit module Show : sig type t = t/2 val print : t -> unit end
  end
|}]


(* Test open *)

open M_with_sig1
module Test_open_with_sig1 : Show with type t = M_with_sig1.t = _

[%%expect{|
Line 2, characters 27-65:
2 | module Test_open_with_sig1 : Show with type t = M_with_sig1.t = _
                               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "Show"

module Test_open_with_sig1 :
  sig type t = M_with_sig1.t val print : t -> unit end
|}]

open M_with_sig2
module Test_open_with_sig2_Fail : Show with type t = M_with_sig2.t = _

[%%expect{|
Line 2, characters 32-70:
2 | module Test_open_with_sig2_Fail : Show with type t = M_with_sig2.t = _
                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Inference of signature sig
                                type t = M_with_sig2.t
                                val print : t -> unit
                              end
       failed as no solution was found.
|}]

open M_with_sig3
module Test_open_with_sig3 : Show with type t = M_with_sig3.t = _

[%%expect{|
Line 2, characters 27-65:
2 | module Test_open_with_sig3 : Show with type t = M_with_sig3.t = _
                               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "Show"

module Test_open_with_sig3 :
  sig type t = M_with_sig3.t val print : t -> unit end
|}]

(* Bug with private *)

module type TMaybePriv = sig type t_maybe_private end

implicit module M = struct type t_maybe_private = private int end

module type S = sig
  type t2
  val print : t2 -> unit
end

implicit module M2 = struct
  type t2 = int
  let print = print_int
end

module type Sol_with_private = sig val v_maybe_private : unit end


implicit module F (M1 : TMaybePriv) (M2 : S)
  : Sol_with_private
  = struct let v_maybe_private = () end

[%%expect{|
module type TMaybePriv = sig type t_maybe_private end
implicit module M : sig type t_maybe_private = private int end
module type S = sig type t2 val print : t2 -> unit end
implicit module M2 : sig type t2 = int val print : int -> unit end
module type Sol_with_private = sig val v_maybe_private : unit end
implicit module F : (M1 : TMaybePriv) (M2 : S) => Sol_with_private
|}]

module Sol_with_private1 : Sol_with_private = _

[%%expect{|
Line 1, characters 25-47:
1 | module Sol_with_private1 : Sol_with_private = _
                             ^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "F(M)(M2)"

module Sol_with_private1 : Sol_with_private
|}]

implicit module F (M1 : TMaybePriv) (M2 : S with type t2 = M1.t_maybe_private)
  : Sol_with_private
  = struct let v_maybe_private = () end

[%%expect{|
implicit module F :
  (M1 : TMaybePriv)
  (M2 : sig type t2 = M1.t_maybe_private val print : t2 -> unit end) =>
    Sol_with_private
|}]

(* Fails because private definition for the first argument of F is used in the
   second argument. *)
module Sol_with_private2_fail : Sol_with_private = _

[%%expect{|
Line 1, characters 30-52:
1 | module Sol_with_private2_fail : Sol_with_private = _
                                  ^^^^^^^^^^^^^^^^^^^^^^
Error: Inference of signature Sol_with_private
       failed as no solution was found.
|}]

implicit module M3 = struct type t_maybe_private = int end

[%%expect{|
implicit module M3 : sig type t_maybe_private = int end
|}]

(* Could succeed because F(M3)(M2) is a valid solution and F(M1)(M2) was
   rejected by the example above. *)
module Sol_with_private3 : Sol_with_private = _

[%%expect{|
Line 1, characters 25-47:
1 | module Sol_with_private3 : Sol_with_private = _
                             ^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "F(M3)(M2)"

module Sol_with_private3 : Sol_with_private
|}]

module FunctorArg {M : Show} : Show with type t = M.t = _

[%%expect{|
Line 1, characters 29-57:
1 | module FunctorArg {M : Show} : Show with type t = M.t = _
                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "M"

module FunctorArg : (M : Show) => sig type t = M.t val print : t -> unit end
|}]

module type Eq = sig
  type t
  val eq : t -> t -> bool
end

module type Ord = sig
  type t
  val cmp : t -> t -> int
  module Eq : Eq with type t = t
end

implicit module EInt : Eq with type t = int = struct
  type t = int
  let eq = Int.equal
end

implicit module EInt2 = EInt

[%%expect{|
module type Eq = sig type t val eq : t -> t -> bool end
module type Ord =
  sig
    type t
    val cmp : t -> t -> int
    module Eq : sig type t = t/2 val eq : t -> t -> bool end
  end
implicit module EInt : sig type t = int val eq : t -> t -> bool end
implicit module EInt2 = EInt
|}]

module EInt3 : Eq with type t = int = _

[%%expect{|
Line 1, characters 13-39:
1 | module EInt3 : Eq with type t = int = _
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "EInt2"

module EInt3 : sig type t = int val eq : t -> t -> bool end
|}]

implicit module OrdToEq (O : Ord) = O.Eq

implicit module OInt = struct
  type t = int
  let cmp = Int.compare
  module Eq = EInt
end

[%%expect{|
implicit module OrdToEq :
  (O : Ord) => sig type t = O.t val eq : t -> t -> bool end
implicit module OInt :
  sig type t = int val cmp : int -> int -> int module Eq = EInt end
|}]

(* Fails because OrdToEq loses module equality. *)
module EInt4 : Eq with type t = int = _

[%%expect{|
Line 1, characters 13-39:
1 | module EInt4 : Eq with type t = int = _
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Inference of signature sig type t = int val eq : t -> t -> bool end
       failed because inference could not make
       any more progress.
       Final state was :
       ?1.
?1 awaited an argument of signature
             sig type t = int val eq : t -> t -> bool end
            It can be filled by either  OrdToEq(OInt)  or  EInt2.

|}]

(* Test abstract functor *)

module type Set = sig
  type t
  type elt
end

implicit module CmpInt : Set.OrderedType with type t = int = Int

implicit module SetMake (X : Set.OrderedType) : Set with type elt = X.t = struct
  type t = X.t list
  type elt = X.t
end

[%%expect{|
module type Set = sig type t type elt end
implicit module CmpInt : sig type t = int val compare : t -> t -> int end
implicit module SetMake :
  (X : Set.OrderedType) => sig type t type elt = X.t end
|}]

module ISet1 : Set with type t = SetMake(CmpInt).t = SetMake(CmpInt)

module ISet : Set with type t = SetMake(CmpInt).t = _

[%%expect{|
module ISet1 : sig type t = SetMake(CmpInt).t type elt end
Line 3, characters 12-53:
3 | module ISet : Set with type t = SetMake(CmpInt).t = _
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 76 [implicit-module-expression]: module expression left implict.
  Infered module expression: "SetMake(CmpInt)"

module ISet : sig type t = SetMake(CmpInt).t type elt end
|}]

(** Test basic absurdity with parametrized type *)

module ParametrizedType = struct

  (* Creates an unknown parametrized type *)
  module type T = sig type _ t end
  implicit module Loop (X : T) = X

  module type Sol = sig val sol : unit -> int -> bool end

  implicit module M (X : T) = struct
  let sol () : int X.t -> int X.t = assert false
  end

  (* Should have the constraints :
    - int ?X.t = int
    - int ?X.t = bool
    Which is absurd.
  *)
  module S : Sol = _

end

[%%expect{|
Line 20, characters 11-20:
20 |   module S : Sol = _
                ^^^^^^^^^
Error: Inference of signature Sol
       failed as no solution was found.
|}]

module RejectUnification = struct
  module type T = sig module T : sig type hole end end
  implicit module Loop (X : T) = X

  module F (X : sig type hole end) : sig type t end = struct
    type t = unit
  end

  implicit module M (X : T) (Y : T) = struct
    type t1 = X.T.hole
    type t2 = Y.T.hole

    type t3 = F(X.T).t
    type t4 = F(Y.T).t
  end

  (* Should have the constraints :
    - ?X.T.hole = int
    - ?Y.T.hole = bool
    - ?X.T = ?Y.T
    Which is absurd.
  *)
  module S : sig
    type t1 = int
    type t2 = bool
    type t3
    type t4 = t3
  end = _
end

[%%expect{|
Lines 23-28, characters 11-9:
23 | ...........: sig
24 |     type t1 = int
25 |     type t2 = bool
26 |     type t3
27 |     type t4 = t3
28 |   end = _
Error: Inference of signature sig
                                type t1 = int
                                type t2 = bool
                                type t3
                                type t4 = t3
                              end
       failed as no solution was found.
|}]

module AcceptParametrizedType = struct
  module type T = sig type t end
  implicit module Loop (X : T) = X

  module type TP = sig type _ t end
  implicit module LoopP (X : TP) = X

  implicit module Sol (A : T) (B : T) (C : TP) = struct
    type t1 = A.t C.t
    type t2 = B.t C.t
  end

  module type S = sig
    type t1 = int list
    type t2 = bool list
  end

  module M : S = Sol (Int) (Bool) (List)

  (* Should have the constraints :
    - A.t C.t = int list
    - B.t C.t = bool list
    Which is solvable.
  *)
  module Test : S = _
end

[%%expect{|
Line 25, characters 14-21:
25 |   module Test : S = _
                   ^^^^^^^
Error: Inference of signature S
       failed because inference could not make
       any more progress.
       Final state was :
       Sol (?1) (?2) (LoopP (?3)).
?1 awaited an argument of signature  T
                                    It can be filled by either  EInt  or
                                    CmpInt.
?2 awaited an argument of signature
                                              T
                                             It can be filled by either
                                             EInt  or  CmpInt.
?3 could be filled with a new recursive call to LoopP
       with no termination guaranty.

|}]

module RejectUnification = struct
  module type T = sig type t end
  implicit module Loop (X : T => T) = X

  module F (X : T => T) : sig type t end = struct
    type t = unit
  end

  module List (X : T) = struct type t = X.t list end

  implicit module M (X : T => T) = struct
    type t1 = X(Int).t

    type t3 = F(X).t
    type t4 = F(List).t
  end

  (* Should have the constraints :
    - ?X(Int).t = bool
    - ?X = List
    Which is absurd.
  *)
  module S : sig
    type t1 = bool
    type t3
    type t4 = t3
  end = _
end

[%%expect{|
Lines 23-27, characters 11-9:
23 | ...........: sig
24 |     type t1 = bool
25 |     type t3
26 |     type t4 = t3
27 |   end = _
Error: Inference of signature sig type t1 = bool type t3 type t4 = t3 end
       failed as no solution was found.
|}]

module InstanceParametrizedConstraint = struct

  module type T = sig type t end
  implicit module Loop (LoopX : T => T) = LoopX

  implicit module M (MX : T => T) (Y : T) = struct
    type t2 = MX(Int).t
    type t1 = MX(Y).t
  end

  module type Sol = (Y : T) => sig
    type t2 = bool
    type t1 = Y.t
  end

  (* Should have the constraints :
    - ?MX(Int).t = bool
    - [Y] ?MX(Y).t = Y.t
    Which is absurd.
  *)
  module S : Sol = _
end

[%%expect{|
Line 21, characters 11-20:
21 |   module S : Sol = _
                ^^^^^^^^^
Error: Inference of signature Sol
       failed as no solution was found.
|}]

module InstanceParametrizedConstraintRev = struct

  module type T = sig type t end
  implicit module Loop (LoopX : T => T) = LoopX

  implicit module M (MX : T => T) (Y : T) = struct
    type t1 = MX(Y).t
    type t2 = MX(Int).t
  end

  module type Sol = (Y : T) => sig
    type t1 = Y.t
    type t2 = bool
  end

  (* Should have the constraints :
    - [Y] ?MX(Y).t = Y.t
    - ?MX(Int).t = bool
    Which is absurd.
  *)
  module S : Sol = _
end

[%%expect{|
Line 21, characters 11-20:
21 |   module S : Sol = _
                ^^^^^^^^^
Error: Inference of signature Sol
       failed as no solution was found.
|}]

module CombineParametrizedConstraint = struct

  module type T = sig type t end
  implicit module Loop (LoopX : T => T) = LoopX

  implicit module M (MX : T => T) (Y : T) = struct
    type t1 = MX(Y).t
    type t2 = MX(Y).t
  end

  module type Sol = (Y : T) => sig
    type t1 = Y.t
    type t2 = bool
  end

  (* Should have the constraints :
    - [Y] ?MX(Y).t = Y.t
    - [Y] ?MX(Y).t = bool
    Which is absurd.
  *)
  module S : Sol = _
end

[%%expect{|
Line 21, characters 11-20:
21 |   module S : Sol = _
                ^^^^^^^^^
Error: Inference of signature Sol
       failed as no solution was found.
|}]

module CombineParametrizedConstraint = struct

  module type T = sig type t end
  implicit module Loop (LoopX : T => T) = LoopX

  implicit module M (MX : T => T) (Y : T) = struct
    type t1 = MX(Y).t
    type t2 = MX(Int).t
  end

  module type Sol = (Y : T) => sig
    type t1
    type t2 = t1
  end

  (* Should have the constraints :
    - [Y] ?MX(Y).t = ?MX(Int).t
    Which is not absurds but means that ?MX drops its argument.
  *)
  module S : Sol = _
end

[%%expect{|
Line 20, characters 11-20:
20 |   module S : Sol = _
                ^^^^^^^^^
Error: Inference of signature Sol
       failed because inference could not make
       any more progress.
       Final state was :
       M (Loop (?1)).
?1 could be filled with a new recursive call to Loop
       with no termination guaranty.

|}]
