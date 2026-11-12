
val negb : bool -> bool

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val copy : 'a1 Marray.t -> 'a1 Marray.t

type uint = Uint63.t

val bdec : bool -> bool

val merge :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t

val msort :
  bool -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t

val inversions_impl : uint Marray.t -> uint

val inversions : uint Marray.t -> uint
