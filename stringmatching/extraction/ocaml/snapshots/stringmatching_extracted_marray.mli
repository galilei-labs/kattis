
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

type char63 = Uint63.t

type string = Pstring.t

val length : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

val fall : string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val build :
  string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val copy :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val scan :
  string -> string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val find_all_impl : string -> string -> uint Marray.t

val find_all : string -> string -> uint Marray.t
