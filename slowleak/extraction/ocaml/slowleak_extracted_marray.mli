
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

val iNF : Uint63.t

val setmin : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val diag_loop : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val edge_loop :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val fw_j :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val fw_i :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val fw_k : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val vx_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val sel_loop :
  Uint63.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t

val rel_loop :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val dij_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t -> Uint63.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t
  option

val slowleak_impl :
  uint -> uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint
  Marray.t -> uint option

val slowleak :
  uint -> uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint
  Marray.t -> uint option
