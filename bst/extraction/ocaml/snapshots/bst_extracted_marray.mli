
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

type color =
| Red
| Black

type rbt =
| RE
| RN of color * rbt * Uint63.t * rbt

val lbal : rbt -> Uint63.t -> rbt -> rbt

val rbal : rbt -> Uint63.t -> rbt -> rbt

val rb_ins : Uint63.t -> rbt -> rbt

val make_black : rbt -> rbt

val rb_insert : Uint63.t -> rbt -> rbt

val around : Uint63.t -> rbt -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val imax : Uint63.t -> Uint63.t -> Uint63.t

val loop :
  uint Marray.t -> Uint63.t -> Uint63.t -> rbt -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val bst_impl : uint Marray.t -> uint Marray.t

val bst : uint Marray.t -> uint Marray.t
