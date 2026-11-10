
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

module Pos :
 sig
  val succ : Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val add_carry : Bigint.t -> Bigint.t -> Bigint.t

  val pred_double : Bigint.t -> Bigint.t

  val mul : Bigint.t -> Bigint.t -> Bigint.t

  val iter : ('a1 -> 'a1) -> 'a1 -> Bigint.t -> 'a1

  val div2 : Bigint.t -> Bigint.t

  val div2_up : Bigint.t -> Bigint.t

  val compare_cont : comparison -> Bigint.t -> Bigint.t -> comparison

  val compare : Bigint.t -> Bigint.t -> comparison
 end

module Z :
 sig
  val double : Bigint.t -> Bigint.t

  val succ_double : Bigint.t -> Bigint.t

  val pred_double : Bigint.t -> Bigint.t

  val pos_sub : Bigint.t -> Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val opp : Bigint.t -> Bigint.t

  val sub : Bigint.t -> Bigint.t -> Bigint.t

  val mul : Bigint.t -> Bigint.t -> Bigint.t

  val compare : Bigint.t -> Bigint.t -> comparison

  val ltb : Bigint.t -> Bigint.t -> bool

  val min : Bigint.t -> Bigint.t -> Bigint.t

  val div2 : Bigint.t -> Bigint.t

  val shiftl : Bigint.t -> Bigint.t -> Bigint.t
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val ltb1 : Float64.t -> Float64.t -> bool

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

val zofi_rec : Uint63.t -> Bigint.t

val zofi : Uint63.t -> Bigint.t

val dal : (Bigint.t * Bigint.t) -> Bigint.t -> Bigint.t

val fex : Float64.t -> Bigint.t * Bigint.t

val expo_step :
  Float64.t array -> Float64.t array -> Uint63.t -> Bigint.t -> Bigint.t

val grid_step :
  Float64.t array -> Float64.t array -> Bigint.t -> Uint63.t -> (Bigint.t
  array * Bigint.t array) -> Bigint.t array * Bigint.t array

val dz : Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t

val key_init :
  Bigint.t array -> Bigint.t array -> Uint63.t -> Bigint.t array -> Bigint.t
  array

val amin_step :
  Uint63.t -> Uint63.t array -> Bigint.t array -> Uint63.t -> Uint63.t ->
  Uint63.t

val relax_step :
  Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t array -> Uint63.t
  -> Uint63.t -> (Bigint.t array * Uint63.t array) -> Bigint.t
  array * Uint63.t array

val prim_step :
  Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t -> ((Uint63.t
  array * Bigint.t array) * Uint63.t array) -> (Uint63.t array * Bigint.t
  array) * Uint63.t array

type dS =
  (((Uint63.t array * Uint63.t array) * Uint63.t) * Uint63.t array) * Uint63.t

val ds_it : dS -> Uint63.t array

val ds_stk : dS -> Uint63.t array

val ds_sp : dS -> Uint63.t

val ds_out : dS -> Uint63.t array

val ds_cnt : dS -> Uint63.t

val dfs_step : Uint63.t -> Uint63.t array -> Uint63.t -> dS -> dS

val tsp_impl : Float64.t array -> Float64.t array -> Uint63.t array

val tsp : Float64.t array -> Float64.t array -> uint array
