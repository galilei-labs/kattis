
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

type char63 = Uint63.t

type string = Pstring.t

val length : string -> Uint63.t

val get : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

val scan :
  string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val purplerain_impl : string -> uint * uint

val purplerain : string -> uint * uint
