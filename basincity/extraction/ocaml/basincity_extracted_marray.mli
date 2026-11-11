
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val exists4 : (Uint63.t -> bool) -> Uint63.t -> bool

val forall4 : (Uint63.t -> bool) -> Uint63.t -> bool

val b2i : bool -> Uint63.t

val count4 : (Uint63.t -> bool) -> Uint63.t -> Uint63.t

val nbr : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val adjb :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool

val alive : Uint63.t Marray.t -> Uint63.t -> bool

val mark1 : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val unmark1 : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val mark :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val unmark :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val deg :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t

val simp :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  bool

val cnt_loop :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val sel_loop :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * bool

val child :
  Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t ->
  bool * Uint63.t Marray.t) -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  bool * Uint63.t Marray.t

val try_slot :
  Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t ->
  bool * Uint63.t Marray.t) -> Uint63.t -> Uint63.t -> Uint63.t ->
  (bool * Uint63.t Marray.t) -> bool * Uint63.t Marray.t

val node :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t ->
  bool * Uint63.t Marray.t) -> Uint63.t -> Uint63.t Marray.t ->
  bool * Uint63.t Marray.t

val search :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t -> bool * Uint63.t Marray.t

val fill_dg :
  Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val put_slot :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val fill_nb :
  Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val basincity_impl : uint -> uint Marray.t Marray.t -> bool

val basincity : uint -> uint Marray.t Marray.t -> bool
