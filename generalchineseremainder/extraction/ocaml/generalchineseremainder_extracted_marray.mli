
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val egcd_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t * Uint63.t

val crt_impl : uint -> uint -> uint -> uint -> (uint * uint) option

val crt : uint -> uint -> uint -> uint -> (uint * uint) option
