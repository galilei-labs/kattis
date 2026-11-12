
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val gcd_loop : Uint63.t -> Uint63.t -> Uint63.t

val gcd63 : Uint63.t -> Uint63.t -> Uint63.t

val pow_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val pow2mod : Uint63.t -> Uint63.t -> Uint63.t

val sum_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val derangement_rotations_impl : uint -> uint -> uint

val derangement_rotations : uint -> uint -> uint
