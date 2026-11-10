
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

  val abs : Bigint.t -> Bigint.t
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val div0 : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb0 : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

type sint = Uint63.t

val zgcd : Bigint.t -> Bigint.t -> Bigint.t

val bdec : bool -> bool

val loop : (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val for_ : Uint63.t -> Uint63.t -> 'a1 -> (Uint63.t -> 'a1 -> 'a1) -> 'a1

val uconv : Uint63.t -> Bigint.t

val sconv : sint -> Bigint.t

val ztab : Uint63.t -> Uint63.t -> sint array array -> Bigint.t array

val upd_row :
  Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t -> Bigint.t -> Bigint.t array
  -> Bigint.t array

val row_gcd : Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t

val div_row :
  Uint63.t -> Uint63.t -> Bigint.t -> Bigint.t array -> Bigint.t array

val norm_row : Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t array

val elim_rows :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t
  array

val find_piv :
  Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array -> bool array -> Uint63.t

val col_step :
  Uint63.t -> Uint63.t -> Uint63.t -> (Bigint.t array * bool array) ->
  Bigint.t array * bool array

val count_nz : Uint63.t -> Uint63.t -> Bigint.t array -> Uint63.t

val valid_impl : uint -> sint array array -> bool

val valid : uint -> sint array array -> bool
