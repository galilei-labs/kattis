
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val ltb : z -> z -> bool

  val min : z -> z -> z

  val div2 : z -> z

  val shiftl : z -> z -> z
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val ltb1 : Float64.t -> Float64.t -> bool

val mul0 : Float64.t -> Float64.t -> Float64.t

val add1 : Float64.t -> Float64.t -> Float64.t

val sub1 : Float64.t -> Float64.t -> Float64.t

val div0 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

val normfr_mantissa : Float64.t -> Uint63.t

val frshiftexp : Float64.t -> Float64.t * Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val zofi_rec : Uint63.t -> z

val zofi : Uint63.t -> z

val dal : (z * z) -> z -> z

val dadd : (z * z) -> (z * z) -> z * z

val dsub : (z * z) -> (z * z) -> z * z

val dmul : (z * z) -> (z * z) -> z * z

val dlt : (z * z) -> (z * z) -> bool

val fex : Float64.t -> z * z

val dex :
  Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> Uint63.t -> z * z

val fd :
  Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> Uint63.t ->
  Float64.t

val gx : Float64.t -> Float64.t -> Float64.t

val c1e5 : Float64.t

val c52 : Float64.t

val cinit : Float64.t

val tol : Float64.t

val key : Float64.t -> Uint63.t -> Float64.t -> Uint63.t

val key_step :
  Float64.t Marray.t -> Float64.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val count_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val prefix_step :
  Uint63.t -> (Uint63.t Marray.t * Uint63.t) -> Uint63.t Marray.t * Uint63.t

val place_step :
  Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) ->
  Uint63.t Marray.t * Uint63.t Marray.t

val min_step :
  Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Float64.t Marray.t
  -> Float64.t Marray.t

val cand_step :
  Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t -> ((Float64.t * Uint63.t) * Uint63.t) ->
  (Float64.t * Uint63.t) * Uint63.t

val cand_cont :
  Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  ((Float64.t * Uint63.t) * Uint63.t) -> bool

val sweep_step :
  Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
  ((Float64.t * Uint63.t) * Uint63.t) -> (Float64.t * Uint63.t) * Uint63.t

val closestpair : Float64.t Marray.t -> Float64.t Marray.t -> uint * uint
