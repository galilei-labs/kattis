
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

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

type char63 = Uint63.t

type string = Pstring.t

val length : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

val mOD : Uint63.t

val capm : Uint63.t -> Uint63.t

val okp : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val pcode : Uint63.t -> Uint63.t -> Uint63.t

val ixi : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val inner :
  string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val middle :
  string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t

val outer :
  string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t

val zapis_impl : string -> uint * bool

val zapis : string -> uint * bool
