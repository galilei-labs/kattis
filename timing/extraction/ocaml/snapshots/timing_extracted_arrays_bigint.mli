
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

  val leb : Bigint.t -> Bigint.t -> bool

  val ltb : Bigint.t -> Bigint.t -> bool

  val min : Bigint.t -> Bigint.t -> Bigint.t

  val div2 : Bigint.t -> Bigint.t

  val shiftl : Bigint.t -> Bigint.t -> Bigint.t

  val shiftr : Bigint.t -> Bigint.t -> Bigint.t
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val abs : Float64.t -> Float64.t

val opp0 : Float64.t -> Float64.t

val ltb1 : Float64.t -> Float64.t -> bool

val leb0 : Float64.t -> Float64.t -> bool

val mul1 : Float64.t -> Float64.t -> Float64.t

val add1 : Float64.t -> Float64.t -> Float64.t

val sub1 : Float64.t -> Float64.t -> Float64.t

val div0 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

val normfr_mantissa : Float64.t -> Uint63.t

val frshiftexp : Float64.t -> Float64.t * Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val wloop : Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val loop : Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val zofi_rec : Uint63.t -> Bigint.t

val zofi : Uint63.t -> Bigint.t

val iofp : Bigint.t -> Uint63.t

val iofz : Bigint.t -> Uint63.t

val fex : Float64.t -> Bigint.t * Bigint.t

val pP : Bigint.t

val oNE : Bigint.t

val fixv : Float64.t -> Bigint.t

val build : Uint63.t -> (Uint63.t -> Bigint.t) -> Bigint.t array

val dot :
  Uint63.t -> Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t ->
  Bigint.t

val naive : Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array

val quad :
  Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t
  array

val madd : Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array

val msub : Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array

val comb :
  Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array
  -> Bigint.t array -> Bigint.t array

val cut : Uint63.t

val splitb : Uint63.t -> bool

val strass : Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array

val mulr : Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array

val ident : Uint63.t -> Bigint.t array

val link_step :
  Uint63.t -> uint array -> uint array -> Float64.t array -> Uint63.t ->
  Bigint.t array -> Bigint.t array

val amat :
  Uint63.t -> Uint63.t -> uint array -> uint array -> Float64.t array ->
  Bigint.t array

val pw :
  Uint63.t -> Uint63.t -> Bigint.t array option -> Bigint.t array -> Bigint.t
  array option

val adj_step :
  Uint63.t -> uint array -> uint array -> Uint63.t -> bool array -> bool array

val faced_z : Uint63.t -> bool array -> Bigint.t array -> Uint63.t -> Bigint.t

val cv : Bigint.t -> Float64.t

val conv : Bigint.t -> Float64.t

val timing_exact :
  uint -> Float64.t array -> uint array -> uint array -> Float64.t array ->
  Float64.t

val link_f :
  uint array -> uint array -> Float64.t array -> Float64.t array -> Uint63.t
  -> Float64.t array -> Float64.t array

val unit_f :
  Uint63.t -> uint array -> uint array -> Float64.t array -> Float64.t array
  -> Float64.t array

val cnt_step :
  uint array -> uint array -> Uint63.t -> Uint63.t array -> Uint63.t array

val faced_f :
  Uint63.t -> bool array -> Float64.t array -> Uint63.t -> Float64.t

val fmin : Float64.t -> Float64.t -> Float64.t

val dlt : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> bool

val f_u : Float64.t

val f_K1 : Float64.t

val f_s30 : Float64.t

val out_step :
  uint array -> uint array -> Float64.t array -> Uint63.t -> Float64.t array
  -> Float64.t array

val coef : Float64.t array -> Uint63.t -> Float64.t

val kx : Uint63.t array -> Uint63.t -> Float64.t

val up : Float64.t -> Float64.t

val elink :
  uint array -> uint array -> Float64.t array -> Float64.t array -> Float64.t
  array -> Uint63.t -> (Float64.t array * Float64.t array) -> Float64.t
  array * Float64.t array

val efort :
  Float64.t array -> Uint63.t array -> Float64.t array -> Float64.t array ->
  Float64.t array -> Float64.t array -> Uint63.t -> (Float64.t array * bool)
  -> Float64.t array * bool

val ebound :
  Uint63.t -> Uint63.t -> uint array -> uint array -> Float64.t array ->
  Float64.t array -> Uint63.t array -> Float64.t array -> Float64.t array ->
  Float64.t array * bool

val tstep :
  Uint63.t -> Uint63.t -> uint array -> uint array -> Float64.t array ->
  Float64.t array -> Uint63.t array -> Uint63.t -> ((Float64.t
  array * Float64.t array) * bool) -> (Float64.t array * Float64.t
  array) * bool

val fpair :
  Uint63.t -> bool array -> Float64.t array -> Float64.t array -> Uint63.t ->
  Float64.t * Float64.t

val fbound :
  Uint63.t -> bool array -> Float64.t array -> Float64.t array -> Float64.t
  -> Uint63.t -> Float64.t

val gmax : Uint63.t -> (Uint63.t -> Float64.t) -> Float64.t

val fcheck : Float64.t -> Float64.t -> bool

val timing_impl :
  uint -> Float64.t array -> uint array -> uint array -> Float64.t array ->
  Float64.t

val timing :
  uint -> Float64.t array -> uint array -> uint array -> Float64.t array ->
  Float64.t
