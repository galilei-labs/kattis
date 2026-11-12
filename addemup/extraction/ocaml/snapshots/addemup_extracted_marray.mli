
val fst : ('a1 * 'a2) -> 'a1

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

val rotd : Uint63.t -> Uint63.t option

val rloop : Uint63.t -> Uint63.t -> Uint63.t option

val alt : Uint63.t -> Uint63.t

val k : Uint63.t

val build :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val merge_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val copy_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val msort :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val lbloop : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val inrange : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val found : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val okv :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val scan :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> bool

val addemup_impl : uint -> uint Marray.t -> bool

val addemup : uint -> uint Marray.t -> bool
