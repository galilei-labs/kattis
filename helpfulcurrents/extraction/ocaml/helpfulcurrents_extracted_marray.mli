
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

type char63 = Uint63.t

type string = Pstring.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

val p : Uint63.t

val addm : Uint63.t -> Uint63.t -> Uint63.t

val orf : Uint63.t -> Uint63.t -> Uint63.t

val pass1 :
  string -> string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t * Uint63.t Marray.t

val pass2 :
  string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * (Uint63.t * Uint63.t)

val rows :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val helpfulcurrents_impl :
  uint -> uint -> uint -> string Marray.t -> uint option

val helpfulcurrents : uint -> uint -> uint -> string Marray.t -> uint option
