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

let () = Clflags.dump_typedtree := true

module SInt2 : Show with type t = int = _

let () = Clflags.dump_typedtree := false

[%%expect{|
[
  structure_item
    Tstr_module (Present)
    SInt2/488
      module_expr
        Tmod_constraint
        module_expr
          Tmod_ident "SInt/290"
        module_type
          Tmty_with
          module_type
            Tmty_ident "Show/283"
          [
            "t/281"
              Twith_type
                type_declaration t/281
                  ptype_params =
                    []
                  ptype_constraints =
                    []
                  ptype_kind =
                    Ttype_abstract
                  ptype_private = Public
                  ptype_manifest =
                    Some
                      core_type
                        Ttyp_constr "int/1!"
                        []
          ]
]

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

(* let () = Clflags.dump_typedtree := true *)

module SIntL = (_ : Show with type t = int list)
module SIntLL : Show with type t = int list list = _

(* let () = Clflags.dump_typedtree := false *)

[%%expect{|
Uncaught exception: Failure("NYI : Inference through functors")

Unexecuted phrases: 1 phrases did not execute due to an error
|}]

(* No solution *)
module SFloat_fail : Show with type t = float = _

[%%expect{|
Uncaught exception: Failure("NYI : Inference through functors")

|}]

(* Shadowing *)

implicit module SInt : Show with type t = float = struct
  type t = float
  let print = print_float
end

module SFloat : Show with type t = float = _

[%%expect{|
implicit module SInt : sig type t = float val print : t -> unit end
Uncaught exception: Failure("NYI : Inference through functors")

|}]

module SInt_fail : Show with type t = int = _

[%%expect{|
Uncaught exception: Failure("NYI : Inference through functors")

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
Error: Inference of signature sig type t = bool val print : t -> unit end
       failed as multiple solutions were found.
|}]

(* Multiple solution because generative *)

implicit module SFloat () : Show with type t = float = struct
  type t = float
  let print = print_float
end

module SFloat_fail : Show with type t = float = _

[%%expect{|
implicit module SFloat : () -> sig type t = float val print : t -> unit end
Uncaught exception: Failure("NYI : Inference through functors")

|}]

(* Ensure no recursive loop *)

module type T = sig val loop : unit end
implicit module LOOP (X : T) = struct let loop = () end

module Loop_fail : T = _

[%%expect{|
module type T = sig val loop : unit end
implicit module LOOP : (X : T) => sig val loop : unit end
Uncaught exception: Failure("NYI : Inference through functors")

|}]

(* Infering a functor *)

module SListBis : (X : Show) -> Show with type t = X.t list = _

[%%expect{|
>> Fatal error: infer_implicit
Uncaught exception: Misc.Fatal_error

|}]

(* Infering a functor using an application *)

implicit module SPair (A : Show) (B : Show) : Show = struct
  type t = A.t * B.t
  let print (a, b) =
    print_string "("; A.print a;
    print_string ", "; B.print b;
    print_string ")"
end

module SIntXPair : (X : Show) -> Show with type t = int * X.t = _

[%%expect{|
implicit module SPair : (A : Show) (B : Show) => Show
>> Fatal error: infer_implicit
Uncaught exception: Misc.Fatal_error

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

implicit module M1 : S1 = struct type t1 = int end

implicit module M2a : S2 = struct type t2 = int end
implicit module M2b : S2 = struct type t2 = bool end

[%%expect{|
module type SSol1 = sig val valid1 : unit end
module type SSol2 = sig val valid2 : unit end
module type S1 = sig type t1 end
module type S2 = sig type t2 end
implicit module F1Imp2 : (X : S1) (Y : sig type t2 = X.t1 end) => SSol1
implicit module F2Imp1 : (X : S2) (Y : sig type t1 = X.t2 end) => SSol2
implicit module M1 : S1
implicit module M2a : S2
implicit module M2b : S2
|}]

module ShouldSucceed1 : SSol1 = _

[%%expect{|
Uncaught exception: Failure("NYI : Inference through functors")

|}]

module ShouldSucceed2 : SSol2 = _

[%%expect{|
Uncaught exception: Failure("NYI : Inference through functors")

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
Uncaught exception: Failure("NYI : Inference through functors")

|}]

(* We remove functors from env to prevent collision later *)
implicit module SList = SInt
implicit module SFloat = SInt
implicit module SPair = SInt

[%%expect{|
implicit module SList = SInt
implicit module SFloat = SInt
implicit module SPair = SInt
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
Error: Inference of signature sig type t = int val print : t -> unit end
       failed as multiple solutions were found.
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
  sig type t module Show : sig type t = t/2 val print : t -> unit end end
module M_with_sig2 :
  sig type t module Show : sig type t = t/2 val print : t -> unit end end
module M_with_sig3 :
  sig type t module Show : sig type t = t/2 val print : t -> unit end end
|}]


(* Test open *)

open M_with_sig1
module Test_open_with_sig1 : Show with type t = M_with_sig1.t = _

[%%expect{|
Line 2, characters 27-65:
2 | module Test_open_with_sig1 : Show with type t = M_with_sig1.t = _
                               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Inference of signature sig
                                type t = M_with_sig1.t
                                val print : t -> unit
                              end
       failed as no solution was found.
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
Error: Inference of signature sig
                                type t = M_with_sig3.t
                                val print : t -> unit
                              end
       failed as no solution was found.
|}]
