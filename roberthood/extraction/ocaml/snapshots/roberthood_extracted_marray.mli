
val negb : bool -> bool



val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val sqrt : Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

type sint = Uint63.t

val bdec : bool -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val encode : Uint63.t -> Uint63.t -> Uint63.t

val kneg : Uint63.t

val cx : Uint63.t -> Uint63.t

val cy : Uint63.t -> Uint63.t

val mcross : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val msq : Uint63.t -> Uint63.t -> Uint63.t

val key_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val merge_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  ((Uint63.t * Uint63.t) * Uint63.t Marray.t) ->
  (Uint63.t * Uint63.t) * Uint63.t Marray.t

val merge :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t

val pass_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t

val merge_pass :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val msort_rec :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val msort : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val dedup_step :
  Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t) -> Uint63.t
  Marray.t * Uint63.t

val neg_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val pops : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val chain_step :
  Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t) -> Uint63.t
  Marray.t * Uint63.t

val chain : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t

val cal_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> ((Uint63.t * Uint63.t) * Uint63.t) -> (Uint63.t * Uint63.t) * Uint63.t

val calipers :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val diam2 : Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t

val roberthood : sint Marray.t -> sint Marray.t -> Float64.t
