
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val lesb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

val iota_loop : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val iota : Uint63.t -> Uint63.t Marray.t

val merge_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val step_end : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val pass_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t

val sort_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val sort_edges : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val find : Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

val findr : Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

val scan :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
  (Uint63.t * Uint63.t Marray.t) option

val mst_impl :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  (Uint63.t * Uint63.t Marray.t) option

val mst :
  uint -> uint Marray.t -> uint Marray.t -> sint Marray.t -> (sint * uint
  Marray.t) option
