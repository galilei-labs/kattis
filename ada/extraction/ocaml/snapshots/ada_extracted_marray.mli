
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val copy : 'a1 Marray.t -> 'a1 Marray.t

type uint = Uint63.t

type sint = Uint63.t

val acopy : Uint63.t Marray.t -> Uint63.t Marray.t

val bdec : bool -> bool

val row_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> bool -> Uint63.t
  Marray.t * bool

val rows_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t

val sum_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val ada_impl : sint Marray.t -> uint * sint

val ada : sint Marray.t -> uint * sint
