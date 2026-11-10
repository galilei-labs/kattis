
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type string = Pstring.t

val cat : string -> string -> string

type uint = Uint63.t

val bdec : bool -> bool

val split_ok : Uint63.t -> Uint63.t -> bool

val mid_of : Uint63.t -> Uint63.t -> Uint63.t

val init_loop : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val ops_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val walk :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t

val build :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> string

val root_of : Uint63.t Marray.t -> Uint63.t -> Uint63.t

val joinstrings_impl :
  string Marray.t -> uint Marray.t -> uint Marray.t -> string

val joinstrings : string Marray.t -> uint Marray.t -> uint Marray.t -> string
