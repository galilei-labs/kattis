
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val sqrt : Float64.t -> Float64.t

val ltb0 : Float64.t -> Float64.t -> bool

val add0 : Float64.t -> Float64.t -> Float64.t

val sub0 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

val zero : Float64.t

type uint = Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

val wloop : Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val loop : Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val dsq : sint Marray.t -> sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val wt :
  sint Marray.t -> sint Marray.t -> uint Marray.t -> Uint63.t -> Uint63.t ->
  Float64.t

val init_step :
  sint Marray.t -> sint Marray.t -> uint Marray.t -> Uint63.t -> Float64.t
  Marray.t -> Float64.t Marray.t

val amin_step :
  Uint63.t -> bool Marray.t -> Float64.t Marray.t -> Uint63.t ->
  (Uint63.t * Float64.t) -> Uint63.t * Float64.t

val upd_step :
  sint Marray.t -> sint Marray.t -> uint Marray.t -> bool Marray.t ->
  Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t

val prim_step :
  sint Marray.t -> sint Marray.t -> uint Marray.t -> Uint63.t -> Uint63.t ->
  ((bool Marray.t * Float64.t Marray.t) * Float64.t) -> (bool
  Marray.t * Float64.t Marray.t) * Float64.t

val comsat : sint Marray.t -> sint Marray.t -> uint Marray.t -> Float64.t

val communicationssatellite :
  sint Marray.t -> sint Marray.t -> uint Marray.t -> Float64.t
