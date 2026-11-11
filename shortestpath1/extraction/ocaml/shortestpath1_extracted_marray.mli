
val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val copy : 'a1 Marray.t -> 'a1 Marray.t

type uint = Uint63.t

val bdec : bool -> bool

val iNF : Uint63.t

val count_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val prefix_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val fill_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t * Uint63.t Marray.t

val sift_up :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val child : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val sift_down :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val pop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val push :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t * Uint63.t Marray.t

type st = { st_dist : Uint63.t Marray.t; st_hk : Uint63.t Marray.t;
            st_hv : Uint63.t Marray.t; st_sz : Uint63.t }

val scan :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  -> st

val main :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> st -> Uint63.t Marray.t

val out_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t option Marray.t ->
  Uint63.t option Marray.t

val dijkstra_impl :
  uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint -> uint
  option Marray.t

val dijkstra :
  uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint -> uint
  option Marray.t
