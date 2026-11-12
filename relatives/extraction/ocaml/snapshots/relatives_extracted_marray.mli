
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

val divout : Uint63.t -> Uint63.t -> Uint63.t

val outer : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val relatives_impl : uint -> uint

val relatives : uint -> uint
