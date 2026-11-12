
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Pos :
 sig
  val succ : Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val add_carry : Bigint.t -> Bigint.t -> Bigint.t

  val pred_double : Bigint.t -> Bigint.t

  val mul : Bigint.t -> Bigint.t -> Bigint.t

  val compare_cont : comparison -> Bigint.t -> Bigint.t -> comparison

  val compare : Bigint.t -> Bigint.t -> comparison

  val eqb : Bigint.t -> Bigint.t -> bool
 end

module Coq_Pos :
 sig
  val succ : Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val add_carry : Bigint.t -> Bigint.t -> Bigint.t

  val mul : Bigint.t -> Bigint.t -> Bigint.t
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

  val to_pos : Bigint.t -> Bigint.t

  val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div : Bigint.t -> Bigint.t -> Bigint.t

  val modulo : Bigint.t -> Bigint.t -> Bigint.t

  val abs : Bigint.t -> Bigint.t
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val div0 : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb0 : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val leb0 : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val div1 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

val zero : Float64.t

type q = { qnum : Bigint.t; qden : Bigint.t }

val inject_Z : Bigint.t -> q

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

type uint = Uint63.t

type sint = Uint63.t

val zgcd : Bigint.t -> Bigint.t -> Bigint.t

val odec : 'a1 option -> 'a1 option

val bdec : bool -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val forl : Uint63.t -> Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> 'a1 -> 'a1

val zofi_rec : Uint63.t -> Bigint.t

val zofi : Uint63.t -> Bigint.t

val zofs : Uint63.t -> Bigint.t

val iofz_rec : Bigint.t -> Uint63.t

val iofz : Bigint.t -> Uint63.t

val qred : q -> q

val qsub : q -> q -> q

val qmul : q -> q -> q

val qltb : q -> q -> bool

val qzerob : q -> bool

type sState = (q array * q array) * Uint63.t array

val sT : sState -> q array

val sO : sState -> q array

val sB : sState -> Uint63.t array

val lc : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val enter : Uint63.t -> bool array -> q array -> Uint63.t option

val lexless :
  q array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> bool

val leave :
  q array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t option

val scale_row : q array -> Uint63.t -> Uint63.t -> q -> q array

val elim_row : q array -> Uint63.t -> Uint63.t -> Uint63.t -> q -> q array

val elim_all :
  q array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> q array

val elim_obj : q array -> q array -> Uint63.t -> Uint63.t -> q -> q array

val pivot : Uint63.t -> Uint63.t -> sState -> Uint63.t -> Uint63.t -> sState

val sloop : Uint63.t -> Uint63.t -> bool array -> sState -> sState

val canon_obj :
  q array -> Uint63.t array -> q array -> Uint63.t -> Uint63.t -> q array

val binit : Uint63.t -> Uint63.t -> Uint63.t array

val cart : Uint63.t -> Uint63.t -> Uint63.t -> q array

val st0 : q array -> Uint63.t -> Uint63.t -> Uint63.t -> sState

val phase1 : q array -> Uint63.t -> Uint63.t -> Uint63.t -> sState

val al2 : q array -> Uint63.t -> Uint63.t -> bool array

val mk2 : sState -> q array -> Uint63.t -> Uint63.t -> sState

val phase2 :
  q array -> Uint63.t -> Uint63.t -> Uint63.t -> sState -> bool array -> q
  array -> q

val fill2 :
  Uint63.t -> (Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t array ->
  Uint63.t array

val flatten : Uint63.t -> Uint63.t array array -> Uint63.t array

val isroad : Uint63.t -> bool

val iNF : Uint63.t

val fw_cell :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t array * Uint63.t
  array) -> Uint63.t array * Uint63.t array

val fw_iter :
  Uint63.t -> Uint63.t -> (Uint63.t array * Uint63.t array) -> Uint63.t
  array * Uint63.t array

val fw : Uint63.t -> Uint63.t array -> Uint63.t array * Uint63.t array

val scan_roads :
  Uint63.t -> Uint63.t array -> (Uint63.t array * Uint63.t array) * Uint63.t

val walk :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
  Uint63.t array -> Uint63.t -> Uint63.t array -> Uint63.t array

val route_cnt :
  Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array
  -> Uint63.t -> Uint63.t -> Uint63.t array

val bound_rows :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> q
  array -> q array

val deliv_row :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t
  array -> Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t
  array -> Uint63.t -> q array -> q array

val build_T :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
  Uint63.t array -> Uint63.t array -> q array

val guard : Uint63.t -> Uint63.t -> bool

val qcost : Uint63.t -> Uint63.t -> Uint63.t array -> bool -> q array

val two36 : Uint63.t

val q2f : q -> Float64.t

val aget : Uint63.t array -> Uint63.t -> Uint63.t

val dq : Uint63.t -> Uint63.t array -> Uint63.t -> Uint63.t -> q

val vq :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
  Uint63.t array -> q array -> sState -> bool array -> Uint63.t -> Uint63.t
  -> bool -> q

val qans :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
  Uint63.t array -> q array -> sState -> bool array -> Uint63.t -> Uint63.t
  -> Float64.t * Float64.t

val answers :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
  Uint63.t array -> q array -> Uint63.t array -> Uint63.t array ->
  (Float64.t * Float64.t) array

val roadtimes_impl :
  sint array array -> uint array -> uint array -> uint array -> uint array ->
  uint array -> (Float64.t * Float64.t) array

val roadtimes :
  sint array array -> uint array -> uint array -> uint array -> uint array ->
  uint array -> (Float64.t * Float64.t) array
