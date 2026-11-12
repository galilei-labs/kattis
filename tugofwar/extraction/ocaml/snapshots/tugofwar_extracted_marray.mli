
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val sum_loop : uint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val cell_loop :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
  Marray.t

val row_loop :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool Marray.t

val item_loop :
  uint Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
  Marray.t

val best_loop :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val tugofwar_impl : uint Marray.t -> uint * uint

val tugofwar : uint Marray.t -> uint * uint
