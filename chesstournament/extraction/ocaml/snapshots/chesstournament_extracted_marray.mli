
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val find : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t

val union :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val unite :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val iota_loop : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val iota : Uint63.t -> Uint63.t Marray.t

val uf_loop :
  Uint63.t Marray.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val rep_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val deg_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t * Uint63.t Marray.t

val pre_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val fill_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t

val init_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t Marray.t * Uint63.t

val inner :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t

val kahn :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> Uint63.t

val chess_impl :
  uint -> uint Marray.t -> bool Marray.t -> uint Marray.t -> bool

val chess_consistent :
  uint -> uint Marray.t -> bool Marray.t -> uint Marray.t -> bool
