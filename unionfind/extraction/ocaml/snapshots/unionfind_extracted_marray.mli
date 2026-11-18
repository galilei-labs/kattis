
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val find : Uint63.t Marray.t -> Uint63.t -> Uint63.t * Uint63.t Marray.t

val link :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val init_loop : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val init_par : Uint63.t -> Uint63.t Marray.t

val scan :
  bool Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> bool
  Marray.t

val run_ops_raw :
  uint -> bool Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t

val count_queries :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val pack_queries :
  bool Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
  Marray.t -> bool Marray.t

val compact_queries : bool Marray.t -> bool Marray.t -> bool Marray.t

val run_ops_impl :
  uint -> bool Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t

val run_ops :
  uint -> bool Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t
