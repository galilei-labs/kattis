
val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

type tree =
| Leaf
| Node of tree * Uint63.t * tree * Uint63.t * Uint63.t

val height : tree -> Uint63.t

val size : tree -> Uint63.t

val mk : tree -> Uint63.t -> tree -> tree

val bal : tree -> Uint63.t -> tree -> tree

val insert : Uint63.t -> tree -> tree

val remove_min : tree -> Uint63.t -> tree -> Uint63.t * tree

val merge : tree -> tree -> tree

val delete : Uint63.t -> tree -> tree

val count_lt : Uint63.t -> tree -> Uint63.t

val kD : Uint63.t

val kE : Uint63.t

val k0 : Uint63.t

val init_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> tree -> Uint63.t
  Marray.t * tree

val ev_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> tree -> Uint63.t Marray.t -> Uint63.t Marray.t

val gcpc_impl : uint -> uint Marray.t -> uint Marray.t -> uint Marray.t

val gcpc : uint -> uint Marray.t -> uint Marray.t -> uint Marray.t
