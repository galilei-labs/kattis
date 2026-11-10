
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type char63 = Uint63.t

type string = Pstring.t

val length0 : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

type sint = Uint63.t

val bdec : bool -> bool

val nEG : Uint63.t

val mONE : Uint63.t

val wt : string -> Uint63.t -> Uint63.t -> Uint63.t

val cnt_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val pre_loop : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val rfill_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val ind_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val q0_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t Marray.t * Uint63.t

val relax1 :
  string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val relax_loop :
  string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  -> ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t

val kahn_loop :
  string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t Marray.t

val excavator_impl :
  string -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t

val excavator : string -> uint Marray.t -> uint Marray.t -> sint
