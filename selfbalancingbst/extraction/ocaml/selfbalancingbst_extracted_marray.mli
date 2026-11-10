
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type sint = Uint63.t

type color =
| Red
| Black

type tree =
| Leaf
| Node of color * tree * Uint63.t * Uint63.t * Uint63.t * tree

val size : tree -> Uint63.t

val node : color -> tree -> Uint63.t -> Uint63.t -> tree -> tree

val key_lt : Uint63.t -> Uint63.t -> bool

val makeBlack : tree -> tree

val makeRed : tree -> tree

val lbal : tree -> Uint63.t -> Uint63.t -> tree -> tree

val rbal : tree -> Uint63.t -> Uint63.t -> tree -> tree

val rbal' : tree -> Uint63.t -> Uint63.t -> tree -> tree

val ins : Uint63.t -> Uint63.t -> tree -> tree

val insert_t : Uint63.t -> Uint63.t -> tree -> tree

val lbalS : tree -> Uint63.t -> Uint63.t -> tree -> tree

val rbalS : tree -> Uint63.t -> Uint63.t -> tree -> tree

val append : tree -> tree -> tree

val del : Uint63.t -> tree -> tree

val delete_t : Uint63.t -> tree -> tree

val find_t : Uint63.t -> tree -> Uint63.t option

val lower_t : Uint63.t -> tree -> Uint63.t option

val upper_t : Uint63.t -> tree -> Uint63.t option

val pred_t : Uint63.t -> tree -> Uint63.t option

val front_t : tree -> Uint63.t option

val back_t : tree -> Uint63.t option

val kth_t : Uint63.t -> tree -> Uint63.t option

val rank_t : Uint63.t -> tree -> Uint63.t

val lookup_t : Uint63.t -> tree -> Uint63.t option

val setv_t : Uint63.t -> Uint63.t -> tree -> tree

val bdec : bool -> bool

val is_out : Uint63.t -> bool

val count_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val on_cur :
  Uint63.t option -> (Uint63.t -> Uint63.t option) -> Uint63.t option

val exec :
  tree Marray.t -> Uint63.t option Marray.t -> Uint63.t option Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((tree
  Marray.t * Uint63.t option Marray.t) * Uint63.t option Marray.t) * Uint63.t

val run_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> tree Marray.t -> Uint63.t option
  Marray.t -> Uint63.t option Marray.t -> Uint63.t -> Uint63.t option Marray.t

val run_impl :
  uint Marray.t -> uint Marray.t -> sint Marray.t -> sint Marray.t -> sint
  option Marray.t

val run_commands :
  uint Marray.t -> uint Marray.t -> sint Marray.t -> sint Marray.t -> sint
  option Marray.t
