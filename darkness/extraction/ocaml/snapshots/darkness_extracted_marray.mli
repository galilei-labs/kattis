
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

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb0 : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val gloop :
  Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val grid_fold :
  Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1) ->
  'a1 -> 'a1

val m48 : Uint63.t

val absdiff : Uint63.t -> Uint63.t -> Uint63.t

val denom :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val lo_sum :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t

val zofint_aux : Uint63.t -> z

val zofint : Uint63.t -> z

val exact_sum :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> z * z

val lit_cell :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> bool

val lit_arr :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
  Marray.t

val flat :
  Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val capf : bool -> bool -> Uint63.t

val init_res : bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val nbr : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val opp : Uint63.t -> Uint63.t

val slot : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val fwd : Uint63.t -> bool

val resid :
  bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val aug :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t

type bst = { bd : Uint63.t Marray.t; bp : Uint63.t Marray.t;
             bq : Uint63.t Marray.t; bt : Uint63.t }

val visit :
  bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> bst -> Uint63.t ->
  Uint63.t -> Uint63.t -> bool -> bst

val bfs_loop :
  bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  bst -> bst

val root_step :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bst -> bst

val roots : bool Marray.t -> Uint63.t -> Uint63.t -> bst

val bfs : bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bst

val is_border : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val fb_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val find_border :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val tmin :
  bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val tapp :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t

val flow_loop :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t

val darkness_impl : uint -> uint -> uint Marray.t Marray.t -> uint

val darkness : uint -> uint -> uint Marray.t Marray.t -> uint
