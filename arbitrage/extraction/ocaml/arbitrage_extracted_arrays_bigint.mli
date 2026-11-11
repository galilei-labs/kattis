
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

  val mul : Bigint.t -> Bigint.t -> Bigint.t

  val pow_pos : Bigint.t -> Bigint.t -> Bigint.t

  val pow : Bigint.t -> Bigint.t -> Bigint.t

  val compare : Bigint.t -> Bigint.t -> comparison

  val ltb : Bigint.t -> Bigint.t -> bool
 end

val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val head0 : Uint63.t -> Uint63.t

val ltb1 : Float64.t -> Float64.t -> bool

val leb0 : Float64.t -> Float64.t -> bool

val mul1 : Float64.t -> Float64.t -> Float64.t

val div0 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

type uint = Uint63.t

val bdec : bool -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val primes : Uint63.t array

val dvd1 : Uint63.t -> Uint63.t -> Uint63.t

val mlt : Uint63.t -> Uint63.t -> Uint63.t

val zofi_rec : Uint63.t -> Bigint.t

val zofi : Uint63.t -> Bigint.t

val ex_step :
  (Uint63.t -> Uint63.t) -> Uint63.t -> ((bool * Bigint.t) * Bigint.t) ->
  (bool * Bigint.t) * Bigint.t

val exact_gt : (Uint63.t -> Uint63.t) -> bool

val f_one : Float64.t

val f_two : Float64.t

val f_c0 : Float64.t

val f_c1 : Float64.t

val cap : Uint63.t

val bIAS : Uint63.t

val mulcell :
  Float64.t -> Uint63.t -> Uint63.t -> Float64.t -> Uint63.t -> Uint63.t ->
  (Float64.t * Uint63.t) * Uint63.t

val ratecell : Uint63.t -> Uint63.t -> (Float64.t * Uint63.t) * Uint63.t

val fcmp :
  Float64.t -> Uint63.t -> Uint63.t -> Float64.t -> Uint63.t -> Uint63.t ->
  bool option

type tabs = { tPR : bool array; tMA : Float64.t array; tEX : Uint63.t array;
              tCN : Uint63.t array; tVT : Uint63.t array }

val wr_head :
  tabs -> Uint63.t -> Float64.t -> Uint63.t -> Uint63.t -> Uint63.t array ->
  tabs

val vadd :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array

val vset :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array

val init_step :
  Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t
  array -> Uint63.t -> tabs -> tabs

val fw_j :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (tabs * bool) -> tabs * bool

val fw_i : Uint63.t -> Uint63.t -> Uint63.t -> (tabs * bool) -> tabs * bool

val fw_k : Uint63.t -> Uint63.t -> (tabs * bool) -> tabs * bool

val arbitrage_impl :
  uint -> uint array -> uint array -> uint array -> uint array -> bool

val arbitrage :
  uint -> uint array -> uint array -> uint array -> uint array -> bool
