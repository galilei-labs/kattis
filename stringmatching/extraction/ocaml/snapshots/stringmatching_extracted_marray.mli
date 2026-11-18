
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type char63 = Uint63.t

type string = Pstring.t

val length0 : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

type buffer = Uint63.t Marray.t * Uint63.t Marray.t

val alen : Uint63.t Marray.t -> Uint63.t

val bget : buffer -> Uint63.t -> Uint63.t

val bset : buffer -> Uint63.t -> Uint63.t -> buffer

val bmake : Uint63.t -> buffer

val bdec : bool -> bool

val fall : string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val build :
  string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val copy : buffer -> buffer -> Uint63.t -> Uint63.t -> buffer

val scan :
  string -> string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> buffer ->
  Uint63.t -> Uint63.t -> Uint63.t -> buffer

val find_all_impl : string -> string -> buffer

val find_all : string -> string -> buffer
