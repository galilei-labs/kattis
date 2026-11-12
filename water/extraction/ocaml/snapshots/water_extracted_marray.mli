
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val add_pipe :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t

val init_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val big : Uint63.t

val scan :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t

val bfs_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t
  Marray.t

val bfs :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val walk :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t -> Uint63.t Marray.t

val augment :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t * Uint63.t

val budget : Uint63.t

val imp_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t

val water_impl :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val water :
  uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t ->
  uint Marray.t -> uint Marray.t -> uint Marray.t
