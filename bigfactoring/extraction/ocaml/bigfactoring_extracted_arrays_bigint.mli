
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

  val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div : Bigint.t -> Bigint.t -> Bigint.t

  val modulo : Bigint.t -> Bigint.t -> Bigint.t

  val even : Bigint.t -> bool

  val abs : Bigint.t -> Bigint.t

  val odd : Bigint.t -> bool
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val ltb0 : Uint63.t -> Uint63.t -> bool

val zgcd : Bigint.t -> Bigint.t -> Bigint.t

val bdec : bool -> bool

val dguard : Bigint.t -> Bigint.t -> bool

val guard : Bigint.t -> Bigint.t -> bool

val pm_loop : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t

val powmod : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t

val strip : Bigint.t -> Uint63.t -> Bigint.t * Uint63.t

val sq_loop : Bigint.t -> Bigint.t -> Uint63.t -> bool

val mr_base : Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t -> bool

val miller_rabin : Bigint.t -> bool

val rho_f : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t

val rho_iter : Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t

val rho_batch :
  Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t ->
  Bigint.t * Bigint.t

val rho_m : Uint63.t

val rho_inner :
  Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t ->
  Uint63.t -> ((Bigint.t * Bigint.t) * Bigint.t) * Bigint.t

val rho_rmax : Uint63.t

val rho_back :
  Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t

val rho_outer :
  Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t

val rho_try : Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t

val rho : Bigint.t -> Bigint.t

val cAP : Uint63.t

val push : Bigint.t array -> Uint63.t -> Bigint.t -> Bigint.t array * Uint63.t

val divout :
  Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> (Bigint.t * Bigint.t
  array) * Uint63.t

val trial :
  Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t ->
  ((Bigint.t * Bigint.t) * Bigint.t array) * Uint63.t

val b0 : Bigint.t

val fallback :
  Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> Bigint.t
  array * Uint63.t

val all_q :
  Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> Uint63.t -> bool

val lucas_ok : Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> bool

val cert_try :
  Bigint.t -> Bigint.t array -> Uint63.t -> Bigint.t -> Uint63.t -> bool

val certify : Bigint.t -> Bigint.t array -> Uint63.t -> bool

val fac :
  Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> Bigint.t
  array * Uint63.t

val copy :
  Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t array

val sink : Bigint.t array -> Uint63.t -> Bigint.t array

val isort : Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t array

val bigfactoring_impl : Bigint.t -> Bigint.t array

val bigfactoring : Bigint.t -> Bigint.t array
