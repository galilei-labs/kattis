
type comparison =
| Eq
| Lt
| Gt

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

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

val compare : string -> string -> comparison

val bdec : bool -> bool

val hloop : string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val khash : Uint63.t -> string -> Uint63.t -> Uint63.t

val kloop : string -> string -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val keq : string -> string -> Uint63.t -> bool

val find : Uint63.t Marray.t -> (Uint63.t -> bool) -> Uint63.t -> Uint63.t

val m_key : Uint63.t

val m_word : Uint63.t

val wbuild :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t Marray.t

val wtest : string Marray.t -> string -> Uint63.t -> bool

val lookup :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> string ->
  Uint63.t

val ktest : string Marray.t -> string -> Uint63.t -> Uint63.t -> bool

val build :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t

val mkb :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t Marray.t -> (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t

val sD :
  ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t

val sP :
  ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t

val sQ :
  ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t

val sT :
  ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t

val sM :
  ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t

val cwalk :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((((Uint63.t
  Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t
  Marray.t) -> (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t

val ploop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((((Uint63.t
  Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t
  Marray.t) -> (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t

val bfs :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> ((((Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t Marray.t) ->
  (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
  Marray.t) * Uint63.t) * Uint63.t Marray.t

val bfs_from :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> (((Uint63.t
  Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t
  Marray.t

val recon :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  string Marray.t -> string Marray.t

val answer2 :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> string -> string Marray.t option

val answer1 :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> string -> string -> string Marray.t option

val qloop :
  string Marray.t -> string Marray.t -> string Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> string Marray.t option Marray.t -> string Marray.t option
  Marray.t

val doublets_impl :
  string Marray.t -> string Marray.t -> string Marray.t -> string Marray.t
  option Marray.t

val doublets :
  string Marray.t -> string Marray.t -> string Marray.t -> string Marray.t
  option Marray.t
