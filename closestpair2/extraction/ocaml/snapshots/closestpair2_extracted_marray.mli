
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val lesb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

val splits : Uint63.t -> Uint63.t -> bool

val midp : Uint63.t -> Uint63.t -> Uint63.t

val merge_loop :
  sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val merge :
  sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t

val msort :
  sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

type res = (Uint63.t * Uint63.t) * Uint63.t

val bd : res -> Uint63.t

val iNF : Uint63.t

val d2 : sint Marray.t -> sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val near : sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val strip_loop :
  sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t

val inner_loop :
  sint Marray.t -> sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> res -> res

val outer_loop :
  sint Marray.t -> sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> res -> res

val solve :
  sint Marray.t -> sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * res

val closestpair_impl : sint Marray.t -> sint Marray.t -> uint * uint

val closestpair : sint Marray.t -> sint Marray.t -> uint * uint
