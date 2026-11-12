
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

type comparison =
| Eq
| Lt
| Gt

val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

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

val midp : Uint63.t -> Uint63.t -> Uint63.t

val cmpt :
  string -> string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  comparison

val copy :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val merge :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val msort :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val iota_loop : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val rank_loop :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t

val r2 : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val keyle :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val sort_round :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val rounds : Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val init_rk :
  string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val build_sa : string -> Uint63.t -> Uint63.t Marray.t

val bs : (Uint63.t -> bool) -> Uint63.t -> Uint63.t -> Uint63.t

val ins :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t Marray.t

val qry :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val depth_loop : Uint63.t -> Uint63.t -> Uint63.t

val build :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t Marray.t

val cmp_at :
  string -> string -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  -> comparison

val answer1 :
  string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> string ->
  Uint63.t -> Uint63.t

val qloop :
  string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> string
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t

val kth_occurrences_impl :
  string -> string Marray.t -> uint Marray.t -> sint Marray.t

val kth_occurrences :
  string -> string Marray.t -> uint Marray.t -> sint Marray.t
