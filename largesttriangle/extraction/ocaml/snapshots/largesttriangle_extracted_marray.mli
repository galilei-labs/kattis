
val fst : ('a1 * 'a2) -> 'a1

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

val div0 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

type uint = Uint63.t

val bdec : bool -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val sH : Uint63.t

val oFF : Uint63.t

val crs :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val merge_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((Uint63.t
  Marray.t * Uint63.t) * Uint63.t) -> (Uint63.t
  Marray.t * Uint63.t) * Uint63.t

val merge :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t

val copy_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val msort :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t Marray.t

val sort : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val dedup_step :
  Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t) -> Uint63.t
  Marray.t * Uint63.t

val decode_step :
  Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) ->
  Uint63.t Marray.t * Uint63.t Marray.t

val popl :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t

val pass_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> (Uint63.t
  Marray.t * Uint63.t) -> Uint63.t Marray.t * Uint63.t

val pass :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t

val rev_step :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val low_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t Marray.t * Uint63.t
  Marray.t

val up_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t
  Marray.t * Uint63.t Marray.t

val climb :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val jloop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val sweep_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t

val sweep : Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

val fzero : Float64.t

val largest_triangle_impl : uint Marray.t -> uint Marray.t -> Float64.t

val largest_triangle : uint Marray.t -> uint Marray.t -> Float64.t
