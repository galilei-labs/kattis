
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

val horner_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val eval_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val diff_inner :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val diff_outer :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val plot_impl : uint -> sint Marray.t -> sint Marray.t

val plot : uint -> sint Marray.t -> sint Marray.t
