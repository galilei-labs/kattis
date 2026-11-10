
val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

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

type command =
| Add of uint * uint
| Query of uint

val bdec : bool -> bool

val nil : Uint63.t

val kl : Uint63.t -> Uint63.t

val kh : Uint63.t -> Uint63.t

val clb : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val vins :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t

val vdel :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t

val vpred :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t

val sup : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val pickc : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val sdown :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val hpush :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val hpop : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val scan :
  command Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t * Uint63.t

val kloop : Uint63.t -> Uint63.t -> Uint63.t

val stab : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val cntloop :
  command Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val pref :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val sess :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t

val mloop :
  command Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val kattissquest_impl : command Marray.t -> uint Marray.t

val kattissquest : command Marray.t -> uint Marray.t
