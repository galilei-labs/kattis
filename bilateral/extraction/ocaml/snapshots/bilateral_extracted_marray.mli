
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val nV : Uint63.t

val nP : Uint63.t

val nM : Uint63.t

val deg_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t

val off_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val fill_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val root_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t

type sres =
| SFound of Uint63.t * Uint63.t Marray.t * Uint63.t Marray.t
| SCont of Uint63.t Marray.t * Uint63.t Marray.t * Uint63.t Marray.t
   * Uint63.t

val scan :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  -> sres

type bres =
| BFound of Uint63.t * Uint63.t Marray.t * Uint63.t Marray.t
| BFail of Uint63.t Marray.t * Uint63.t Marray.t

val bfs :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  bres

val walk :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val phases :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val mark_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val engine :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val cnt_loop : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val out_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val count_marks : Uint63.t Marray.t -> Uint63.t

val build : Uint63.t Marray.t -> Uint63.t Marray.t

val bilateral_impl : uint Marray.t -> uint Marray.t -> uint Marray.t

val bilateral : uint Marray.t -> uint Marray.t -> uint Marray.t
