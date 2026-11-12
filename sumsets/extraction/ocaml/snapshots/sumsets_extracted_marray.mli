
val negb : bool -> bool



val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val lesb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type sint = Uint63.t

type big = { b0 : Uint63.t Marray.t; b1 : Uint63.t Marray.t;
             b2 : Uint63.t Marray.t; b3 : Uint63.t Marray.t }

val chunk : big -> Uint63.t -> Uint63.t Marray.t

val upd : big -> Uint63.t -> Uint63.t Marray.t -> big

val bget : big -> Uint63.t -> Uint63.t

val bset : big -> Uint63.t -> Uint63.t -> big

val clen : Uint63.t -> Uint63.t -> Uint63.t

val bmake : Uint63.t -> Uint63.t -> big

val hA : Uint63.t

val hash : Uint63.t -> Uint63.t -> Uint63.t

val bdec : bool -> bool

val code : Uint63.t -> Uint63.t -> Uint63.t

val chk :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> bool

val walk :
  Uint63.t Marray.t -> big -> big -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> bool

type tbl = { th : big; tn : big; tc : big; tk : Uint63.t }

val ins : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> tbl -> tbl

val build_in :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> tbl ->
  tbl

val build_out :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> tbl -> tbl

val query :
  Uint63.t Marray.t -> tbl -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  bool

val any_l :
  Uint63.t Marray.t -> tbl -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  bool

val best_k :
  Uint63.t Marray.t -> tbl -> Uint63.t -> Uint63.t -> Uint63.t -> bool ->
  Uint63.t -> Uint63.t option

val sumsets_impl : Uint63.t Marray.t -> Uint63.t option

val sumsets : sint Marray.t -> sint option
