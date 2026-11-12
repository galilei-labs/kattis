
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val copy : 'a1 Marray.t -> 'a1 Marray.t

type uint = Uint63.t

val bdec : bool -> bool

val sift : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val build : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val huff : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val canvas_impl : uint Marray.t -> uint

val canvas : uint Marray.t -> uint
