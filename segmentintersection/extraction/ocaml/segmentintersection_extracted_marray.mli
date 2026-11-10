
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val lesb : Uint63.t -> Uint63.t -> bool

type sint = Uint63.t

type 'a inter =
| Empty
| Point of 'a * 'a * 'a
| Segment of 'a * 'a * 'a * 'a

val lexle_m : sint -> sint -> sint -> sint -> bool

val lexlt_m : sint -> sint -> sint -> sint -> bool

val finish_m : sint -> sint -> sint -> sint -> sint inter

val coll2_m :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter

val coll1_m :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter

val coll_m :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter

val onseg_m : sint -> sint -> sint -> sint -> sint -> sint -> bool

val cross_fin_m :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter

val crossing_m :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter

val isect_m :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter

val intersect :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter
