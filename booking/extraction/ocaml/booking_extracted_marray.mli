
val negb : bool -> bool



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

type 'a datetime = { year : 'a; month : 'a; day : 'a; hour : 'a; minute : 'a }

val bdec : bool -> bool

val swap : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val part_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t * Uint63.t

val partition :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t

val qsort : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val sort_all : Uint63.t Marray.t -> Uint63.t Marray.t

val sweep :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t

val leapb : Uint63.t -> bool

val days_before_year : Uint63.t -> Uint63.t

val days_before_month : Uint63.t -> Uint63.t -> Uint63.t

val mach_minutes : uint datetime -> Uint63.t

val key_al : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val key_rh : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val fill :
  uint datetime Marray.t -> uint datetime Marray.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val min_rooms_impl :
  uint -> uint datetime Marray.t -> uint datetime Marray.t -> uint

val min_rooms :
  uint -> uint datetime Marray.t -> uint datetime Marray.t -> uint
