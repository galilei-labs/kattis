
val fst : ('a1 * 'a2) -> 'a1

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val split_ok : Uint63.t -> Uint63.t -> bool

val midp : Uint63.t -> Uint63.t -> Uint63.t

val take_left :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val merge_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val copy_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val msort :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val need : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val max_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t

val dirtydriving_impl : uint -> uint Marray.t -> uint

val dirtydriving : uint -> uint Marray.t -> uint
