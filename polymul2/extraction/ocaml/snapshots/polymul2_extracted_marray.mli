
val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

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

val sqrt : Float64.t -> Float64.t

val opp : Float64.t -> Float64.t

val mul0 : Float64.t -> Float64.t -> Float64.t

val add0 : Float64.t -> Float64.t -> Float64.t

val sub0 : Float64.t -> Float64.t -> Float64.t

val div : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

val normfr_mantissa : Float64.t -> Uint63.t

val frshiftexp : Float64.t -> Float64.t * Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

val wloop : Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val loop : Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val lg_find : Uint63.t -> Uint63.t -> Uint63.t

val log2up : Uint63.t -> Uint63.t

val tw_cell :
  Uint63.t -> Uint63.t -> Float64.t -> Float64.t -> Uint63.t -> (Float64.t
  Marray.t * Float64.t Marray.t) -> Float64.t Marray.t * Float64.t Marray.t

val tw_stage :
  Uint63.t -> (((Float64.t Marray.t * Float64.t
  Marray.t) * Float64.t) * Float64.t) -> ((Float64.t Marray.t * Float64.t
  Marray.t) * Float64.t) * Float64.t

val build_tw : Uint63.t -> Uint63.t -> Float64.t Marray.t * Float64.t Marray.t

val bfly :
  Uint63.t -> Uint63.t -> Uint63.t -> bool -> Float64.t Marray.t -> Float64.t
  Marray.t -> Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t ->
  (Float64.t Marray.t * Float64.t Marray.t) -> Float64.t Marray.t * Float64.t
  Marray.t

val fft_stage :
  Uint63.t -> Uint63.t -> bool -> Float64.t Marray.t -> Float64.t Marray.t ->
  Uint63.t -> (((Float64.t Marray.t * Float64.t Marray.t) * Float64.t
  Marray.t) * Float64.t Marray.t) -> ((Float64.t Marray.t * Float64.t
  Marray.t) * Float64.t Marray.t) * Float64.t Marray.t

val fft :
  Uint63.t -> Uint63.t -> bool -> Float64.t Marray.t -> Float64.t Marray.t ->
  Float64.t Marray.t -> Float64.t Marray.t -> Float64.t Marray.t * Float64.t
  Marray.t

val kOFF : Uint63.t

val limb : Uint63.t -> Uint63.t -> Float64.t

val load :
  sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t

val copy_out :
  Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
  (Float64.t Marray.t * Float64.t Marray.t) -> Float64.t Marray.t * Float64.t
  Marray.t

val nL : Uint63.t

val fwd_all :
  sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t ->
  Float64.t Marray.t -> Float64.t Marray.t * Float64.t Marray.t

val cacc :
  Float64.t -> Float64.t -> Float64.t -> Float64.t -> (Float64.t * Float64.t)
  -> Float64.t * Float64.t

val pterm :
  Uint63.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t
  Marray.t -> Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t ->
  (Float64.t * Float64.t) -> Float64.t * Float64.t

val pcell :
  Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
  Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> (Float64.t
  Marray.t * Float64.t Marray.t) -> Float64.t Marray.t * Float64.t Marray.t

val products :
  Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
  Float64.t Marray.t -> Float64.t Marray.t -> Float64.t Marray.t * Float64.t
  Marray.t

val mAGIC : Float64.t

val mAGICI : Uint63.t

val toint : Float64.t -> Uint63.t

val accum :
  Uint63.t -> Uint63.t -> Float64.t -> Float64.t Marray.t -> Float64.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val polymul_impl : sint Marray.t -> sint Marray.t -> sint Marray.t

val polymul : sint Marray.t -> sint Marray.t -> sint Marray.t
