
val lxor0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val xor_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val odd_one_impl : uint Marray.t -> uint

val odd_one : uint Marray.t -> uint
