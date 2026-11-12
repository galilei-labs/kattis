
val negb : bool -> bool

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type 'a token =
| Open
| Close
| Num of 'a

val bdec : bool -> bool

val mi : Uint63.t

val opm : bool -> Uint63.t -> Uint63.t -> Uint63.t

val idm : bool -> Uint63.t

val loop :
  uint token Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool -> Uint63.t
  Marray.t -> Uint63.t

val bracketsequence_impl : uint token Marray.t -> uint

val bracketsequence : uint token Marray.t -> uint
