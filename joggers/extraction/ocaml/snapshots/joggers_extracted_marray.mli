
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val ep :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val oth :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val eid : Uint63.t -> Uint63.t -> Uint63.t

val lamp_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t -> bool Marray.t

val cnt_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t

val off_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val fill_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t

type bst = { vis : bool Marray.t; dst : Uint63.t Marray.t;
             par : Uint63.t Marray.t; pe : Uint63.t Marray.t;
             ord : Uint63.t Marray.t; tl : Uint63.t }

val scan_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bst ->
  bst

val bfs_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> bst -> bst

val sweep_loop :
  Uint63.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> bool Marray.t -> Uint63.t -> Uint63.t

val joggers_impl :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t

val joggers :
  uint -> uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint
  Marray.t -> uint
