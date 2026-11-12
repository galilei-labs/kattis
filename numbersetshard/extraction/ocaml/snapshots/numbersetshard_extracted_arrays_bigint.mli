
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val mark :
  bool array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool array

val mark_from : bool array -> Uint63.t -> Uint63.t -> bool array

val sieve : bool array -> Uint63.t -> Uint63.t -> Uint63.t -> bool array

val find :
  Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t * Uint63.t array

val union :
  Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t
  array * Uint63.t array

val ulink :
  Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t array * Uint63.t array

val first_off : Uint63.t -> Uint63.t -> Uint63.t

val uprimes :
  bool array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array ->
  Uint63.t array -> Uint63.t -> Uint63.t array * Uint63.t array

val iota : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array

val count : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val numbersets_impl : uint -> uint -> uint -> uint

val numbersets : uint -> uint -> uint -> uint
