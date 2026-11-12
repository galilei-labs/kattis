
val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val k : Uint63.t

val mask : Uint63.t

val gen_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
  ((Uint63.t array * Uint63.t) * Uint63.t array) * Uint63.t array

val prefix_loop : Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array

val place_loop :
  Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t -> Uint63.t array ->
  Uint63.t array -> Uint63.t array

val pass :
  Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array
  -> Uint63.t array

val hash_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array
  -> Uint63.t

val magic_impl :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val magic : uint -> uint -> uint -> uint -> uint -> uint -> uint
