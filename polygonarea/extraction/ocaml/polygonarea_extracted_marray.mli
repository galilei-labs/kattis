
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val length : 'a1 Marray.t -> Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

val area_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t

val signed_area2_impl : sint Marray.t -> sint Marray.t -> sint

val signed_area2 : sint Marray.t -> sint Marray.t -> sint
