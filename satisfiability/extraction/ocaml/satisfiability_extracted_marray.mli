
val negb : bool -> bool

val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val lor0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type 'a literal =
| X of 'a
| NotX of 'a

val bdec : bool -> bool

val bitof : Uint63.t -> Uint63.t

val lit_bits : bool -> uint literal -> Uint63.t

val mask_loop :
  bool -> uint literal Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val clause_mask : bool -> uint literal Marray.t -> Uint63.t

val fill_loop :
  bool -> uint literal Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val masks : bool -> uint literal Marray.t Marray.t -> Uint63.t Marray.t

val clause_ok : Uint63.t -> Uint63.t -> Uint63.t -> bool

val check_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> bool

val check_all :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool

val search_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> bool

val satisfiable_impl : Uint63.t -> uint literal Marray.t Marray.t -> bool

val satisfiable : uint -> uint literal Marray.t Marray.t -> bool
