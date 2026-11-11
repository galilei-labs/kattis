
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val vol : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val upd :
  ((Uint63.t * Uint63.t) * Uint63.t) -> Uint63.t ->
  (Uint63.t * Uint63.t) * Uint63.t

val scan :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  ((Uint63.t * Uint63.t) * Uint63.t) -> (Uint63.t * Uint63.t) * Uint63.t

val egcd :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t * Uint63.t

val merge :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val lift : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val rr_impl : uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint

val remainderreminder :
  uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint
