
type comparison =
| Eq
| Lt
| Gt

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type string = Pstring.t

val compare : string -> string -> comparison

type uint = Uint63.t

val bdec : bool -> bool

val midp : Uint63.t -> Uint63.t -> Uint63.t

val lb : string Marray.t -> string -> Uint63.t -> Uint63.t -> Uint63.t

val look : string Marray.t -> Uint63.t -> string -> Uint63.t

val shift : string Marray.t -> Uint63.t -> Uint63.t -> string Marray.t

val is_eq : comparison -> bool

val insert :
  string Marray.t -> Uint63.t -> string -> string Marray.t * Uint63.t

val build :
  string Marray.t -> string Marray.t -> Uint63.t -> Uint63.t -> string
  Marray.t -> Uint63.t -> string Marray.t * Uint63.t

val fill :
  string Marray.t -> string Marray.t -> string Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> bool Marray.t -> bool Marray.t

val okc :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t -> bool

val lim : Uint63.t -> Uint63.t -> Uint63.t

val bump : Uint63.t -> Uint63.t -> Uint63.t

val srch :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> bool * Uint63.t Marray.t

val deepen :
  bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t

val committees_impl : uint -> string Marray.t -> string Marray.t -> uint

val committees : uint -> string Marray.t -> string Marray.t -> uint
