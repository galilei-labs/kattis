
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type char63 = Uint63.t

type string = Pstring.t

val length0 : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

val lowb : Uint63.t -> Uint63.t

val fen_add :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val fen_sum : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val imin : Uint63.t -> Uint63.t -> Uint63.t

val hcond : string -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val expand : string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val man :
  string -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t Marray.t

val manacher : string -> Uint63.t Marray.t

val tab_loop :
  (Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val tab : Uint63.t -> (Uint63.t -> Uint63.t) -> Uint63.t Marray.t

val build :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val fadd :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val fsum : Uint63.t Marray.t -> Uint63.t -> Uint63.t

val fval : (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t -> Uint63.t

val walk :
  Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val insert :
  Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t * Uint63.t Marray.t

val sweep :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t
  Marray.t * Uint63.t Marray.t) -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t

val lsum_all :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val fam :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> bool -> Uint63.t Marray.t

val palindromes_impl :
  string -> uint Marray.t -> uint Marray.t -> uint Marray.t

val palindromes : string -> uint Marray.t -> uint Marray.t -> uint Marray.t
