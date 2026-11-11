
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val lesb : Uint63.t -> Uint63.t -> bool

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val length : 'a1 Marray.t -> Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

type tree =
| Leaf
| Node of tree * Uint63.t * Uint63.t * tree * Uint63.t

val height : tree -> Uint63.t

val hmax : Uint63.t -> Uint63.t -> Uint63.t

val node : tree -> Uint63.t -> Uint63.t -> tree -> tree

val bal : tree -> Uint63.t -> Uint63.t -> tree -> tree

val insert : Uint63.t -> Uint63.t -> tree -> tree

val remove_min :
  tree -> Uint63.t -> Uint63.t -> tree -> (Uint63.t * Uint63.t) * tree

val merge : tree -> tree -> tree

val remove : Uint63.t -> tree -> tree

val between : Uint63.t -> Uint63.t -> tree -> bool

val build :
  sint Marray.t -> sint Marray.t -> Uint63.t -> Uint63.t -> tree -> tree

val step :
  Uint63.t -> sint Marray.t -> sint Marray.t -> Uint63.t -> tree -> tree
  option

val sweep :
  Uint63.t -> sint Marray.t -> sint Marray.t -> tree -> tree -> tree option

val intersecting_rectangles_impl :
  sint Marray.t -> sint Marray.t -> sint Marray.t -> sint Marray.t -> bool

val intersecting_rectangles :
  sint Marray.t -> sint Marray.t -> sint Marray.t -> sint Marray.t -> bool
