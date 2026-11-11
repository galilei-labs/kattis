
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val lxor0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val hmul : Uint63.t

val hidx : Uint63.t -> Uint63.t -> Uint63.t

val find : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val find0 : Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

val lookup : Uint63.t -> Uint63.t Marray.t -> Uint63.t -> bool

val insert :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * bool

val key : Uint63.t -> Uint63.t -> Uint63.t

val pdfs :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> bool

val leafins :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t Marray.t * bool

val idfs :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t * bool

val search_m :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val mloop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val fill :
  Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val logcap : Uint63.t -> Uint63.t

val indoor : uint Marray.t Marray.t -> uint -> bool

val indoorienteering : uint Marray.t Marray.t -> uint -> bool
