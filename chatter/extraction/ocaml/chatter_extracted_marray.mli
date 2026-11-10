
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

type uint = Uint63.t

val bdec : bool -> bool

val nx : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val redraw :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  (Uint63.t * Uint63.t) * Uint63.t

val relabel :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t

val merge :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> ((Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t Marray.t) * Uint63.t Marray.t

val union :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> ((Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t Marray.t) * Uint63.t Marray.t

val sim :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val init :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val tally :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t * Uint63.t Marray.t

val countd : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

val fill :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  (Uint63.t * Uint63.t) Marray.t -> (Uint63.t * Uint63.t) Marray.t

val chatter_impl :
  uint -> uint -> uint -> uint -> uint -> uint * (uint * uint) Marray.t

val chatter :
  uint -> uint -> uint -> uint -> uint -> uint * (uint * uint) Marray.t
