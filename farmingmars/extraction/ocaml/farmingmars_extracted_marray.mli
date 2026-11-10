
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val ltb0 : Float64.t -> Float64.t -> bool

val leb0 : Float64.t -> Float64.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val iota : Uint63.t -> Uint63.t Marray.t

val merge_step :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> ((Uint63.t * Uint63.t) * Uint63.t Marray.t) ->
  (Uint63.t * Uint63.t) * Uint63.t Marray.t

val merge :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val seg_mid : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val pass :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t

val msort : (Uint63.t -> Uint63.t -> bool) -> Uint63.t -> Uint63.t Marray.t

val bs :
  Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t -> Uint63.t ->
  Uint63.t -> Uint63.t

val lbound :
  Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Float64.t -> Uint63.t

val mk_ids :
  Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val blk : Uint63.t -> Uint63.t

val mo_le :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> bool

val add0 :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t * Uint63.t Marray.t

val rem :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t * Uint63.t Marray.t

val move :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> ((Uint63.t * Uint63.t) * Uint63.t
  Marray.t) * Uint63.t Marray.t

val mo_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> ((((Uint63.t * Uint63.t) * Uint63.t
  Marray.t) * Uint63.t Marray.t) * bool Marray.t) ->
  (((Uint63.t * Uint63.t) * Uint63.t Marray.t) * Uint63.t Marray.t) * bool
  Marray.t

val farm :
  Float64.t Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t

val farmingmars :
  Float64.t Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t
