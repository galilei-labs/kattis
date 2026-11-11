
val fst : ('a1 * 'a2) -> 'a1

val lxor0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type player =
| Ruben
| Albert

val opponent : player -> player

val bdec : bool -> bool

val loop : (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val for_ : (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val imin : Uint63.t -> Uint63.t -> Uint63.t

val imax : Uint63.t -> Uint63.t -> Uint63.t

val cidx : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val look :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val cutv :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val mark_c :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val mark_b :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val mark_a :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val mex_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val cell :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t
  Marray.t * Uint63.t Marray.t) -> Uint63.t Marray.t * Uint63.t Marray.t

val table : Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val winner_impl :
  player -> uint Marray.t -> uint Marray.t -> uint Marray.t -> player

val winner :
  player -> uint Marray.t -> uint Marray.t -> uint Marray.t -> player
