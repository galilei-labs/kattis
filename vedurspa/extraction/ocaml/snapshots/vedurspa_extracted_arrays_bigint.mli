
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

  val eqb : Bigint.t -> Bigint.t -> bool
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

  val leb : Bigint.t -> Bigint.t -> bool

  val ltb : Bigint.t -> Bigint.t -> bool

  val eqb : Bigint.t -> Bigint.t -> bool

  val max : Bigint.t -> Bigint.t -> Bigint.t

  val min : Bigint.t -> Bigint.t -> Bigint.t

  val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div : Bigint.t -> Bigint.t -> Bigint.t

  val div2 : Bigint.t -> Bigint.t

  val shiftl : Bigint.t -> Bigint.t -> Bigint.t
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val div0 : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb0 : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val leb0 : Uint63.t -> Uint63.t -> bool

val opp0 : Float64.t -> Float64.t

val ltb1 : Float64.t -> Float64.t -> bool

val mul1 : Float64.t -> Float64.t -> Float64.t

val div1 : Float64.t -> Float64.t -> Float64.t

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

val zofi_rec : Uint63.t -> Bigint.t

val zofi : Uint63.t -> Bigint.t

val pos2int : Bigint.t -> Uint63.t

val z2int : Bigint.t -> Uint63.t

val fex : Float64.t -> Bigint.t * Bigint.t

val fconv : Float64.t option -> (Bigint.t * Bigint.t) option

val iconv : uint option -> (Bigint.t * Bigint.t) option

type sums = { sP : Bigint.t; sK : Bigint.t; sKK : Bigint.t; sY : Bigint.t;
              sKY : Bigint.t; sG : Bigint.t }

val sums0 : sums

val acc_step :
  ('a1 -> (Bigint.t * Bigint.t) option) -> 'a1 array -> Uint63.t -> sums ->
  sums

val col_sums : ('a1 -> (Bigint.t * Bigint.t) option) -> 'a1 array -> sums

type fitr = { fc0 : Bigint.t; fc1 : Bigint.t; fden : Bigint.t }

val fit : sums -> Bigint.t -> fitr option

val rnd_at : fitr -> Bigint.t -> Bigint.t

val clampZ : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t

val fl_of_Z : Bigint.t -> Float64.t

val c20 : Float64.t

val fout : fitr option -> Bigint.t -> Bigint.t -> Bigint.t -> Float64.t option

val iout : fitr option -> Bigint.t -> Bigint.t -> Bigint.t -> uint option

type out =
  ((Float64.t option array * uint option array) * Float64.t option
  array) * uint option array

val out_step :
  fitr option -> fitr option -> fitr option -> fitr option -> Bigint.t ->
  Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> out -> out

val vedurspa_impl :
  Float64.t option array -> uint option array -> Float64.t option array ->
  uint option array -> uint -> out

val vedurspa :
  Float64.t option array -> uint option array -> Float64.t option array ->
  uint option array -> uint -> ((Float64.t option array * uint option
  array) * Float64.t option array) * uint option array
