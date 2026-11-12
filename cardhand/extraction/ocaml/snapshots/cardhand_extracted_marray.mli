
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

type char63 = Uint63.t

type string = Pstring.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

val imax : Uint63.t -> Uint63.t -> Uint63.t

val sidx_m : Uint63.t -> Uint63.t

val rank_m : Uint63.t -> Uint63.t

val pw4 : Uint63.t -> Uint63.t

val pw2 : Uint63.t -> Uint63.t

val sg_m : Uint63.t -> Uint63.t -> Uint63.t

val dr_m : Uint63.t -> Uint63.t -> Uint63.t

val key_m : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val inj_m : Uint63.t -> bool

val prep :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val keys :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t
  Marray.t

val compact :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t

val dp :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t

val lcs_for :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

val search :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t

val min_moves_impl : string Marray.t -> uint

val min_moves : string Marray.t -> uint
