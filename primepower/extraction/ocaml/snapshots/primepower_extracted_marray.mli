
val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val is_zero : Uint63.t -> bool

val is_even : Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

type uint = Uint63.t

val bdec : bool -> bool

val m : Uint63.t

val pow_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val powmod : Uint63.t -> Uint63.t -> Uint63.t

val cross_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val sieve_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val sieve : Uint63.t -> Uint63.t Marray.t

val prod_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val primepower_impl : uint -> uint -> uint -> uint

val primepower : uint -> uint -> uint -> uint
