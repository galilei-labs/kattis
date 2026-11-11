
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

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

val guard : Uint63.t -> Uint63.t -> Uint63.t -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val merge_step :
  Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> ((Uint63.t * Uint63.t) * Uint63.t Marray.t) ->
  (Uint63.t * Uint63.t) * Uint63.t Marray.t

val merge :
  Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t

val copy_step :
  Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t
  Marray.t * Uint63.t Marray.t

val merge_copy :
  Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val msort_rec :
  Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val iota_step : Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val scan_cont :
  Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t -> Uint63.t ->
  (((Uint63.t * bool) * Float64.t) * Uint63.t) -> bool

val scan_step :
  Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  (((Uint63.t * bool) * Float64.t) * Uint63.t) ->
  ((Uint63.t * bool) * Float64.t) * Uint63.t

val adv : Uint63.t -> Uint63.t -> Uint63.t -> bool

val sweep :
  Float64.t Marray.t -> Float64.t Marray.t -> Float64.t -> Uint63.t Marray.t
  -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t -> Uint63.t Marray.t ->
  (Uint63.t Marray.t * Uint63.t) option

val copy_out :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val cover :
  Float64.t -> Float64.t -> Float64.t Marray.t -> Float64.t Marray.t -> uint
  Marray.t option
