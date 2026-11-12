
val negb : bool -> bool



val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type sint = Uint63.t

type 'd answer =
| Dist of 'd
| Impossible
| MinusInfinity

val bdec : bool -> bool

val iNF : Uint63.t

val relax :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t Marray.t -> bool -> Uint63.t Marray.t * bool

val edges_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> bool -> Uint63.t Marray.t * bool

val rounds_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val seed_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t

val build_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val adj_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t

val bfs_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t

val answer_of :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t answer

val ans_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t answer Marray.t -> Uint63.t answer Marray.t

val shortestpath3_impl :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t answer Marray.t

val shortestpath3 :
  uint -> uint -> uint Marray.t -> uint Marray.t -> sint Marray.t -> uint
  Marray.t -> sint answer Marray.t
