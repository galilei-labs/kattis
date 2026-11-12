
val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mulc : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type char63 = Uint63.t

type string = Pstring.t

val length0 : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

val p61 : Uint63.t

val mulmod : Uint63.t -> Uint63.t -> Uint63.t

val addmod : Uint63.t -> Uint63.t -> Uint63.t

val submod : Uint63.t -> Uint63.t -> Uint63.t

val bdec : bool -> bool

val pre_loop :
  Uint63.t -> string -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t Marray.t

val pow_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t Marray.t

val prefix_hashes : Uint63.t -> string -> Uint63.t -> Uint63.t Marray.t

val powers : Uint63.t -> Uint63.t -> Uint63.t Marray.t

val hash :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val q_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val hashes_impl :
  uint -> string -> uint Marray.t -> uint Marray.t -> uint Marray.t

val hashes : uint -> string -> uint Marray.t -> uint Marray.t -> uint Marray.t
