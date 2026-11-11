
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

val prime : Uint63.t

val hash_loop :
  Uint63.t -> string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val hash : Uint63.t -> string -> Uint63.t

val seed : Uint63.t

val rng_next : Uint63.t -> Uint63.t

val rng_draw : Uint63.t -> Uint63.t

val count_loop :
  Uint63.t -> Uint63.t -> string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val sumsq_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val level1 :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t -> ((Uint63.t * Uint63.t) * Uint63.t
  Marray.t) * Uint63.t Marray.t

val layout_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t

val distribute :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t

val place_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t * bool

val clear_loop :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val level2 :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  (Uint63.t Marray.t * Uint63.t) * Uint63.t

val buckets_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t * Uint63.t Marray.t

type tables = { t_a1 : Uint63.t; t_nb : Uint63.t; t_meta : Uint63.t Marray.t;
                t_slot : Uint63.t Marray.t }

val build : string Marray.t -> Uint63.t -> tables

val pos : tables -> string -> Uint63.t

val check_loop : tables -> string Marray.t -> Uint63.t -> Uint63.t -> bool

val scan_loop : string Marray.t -> string -> Uint63.t -> Uint63.t -> Uint63.t

val query :
  string Marray.t -> string Marray.t -> Uint63.t -> bool -> tables -> string
  -> string option

val fill_loop :
  string Marray.t -> string Marray.t -> string Marray.t -> Uint63.t -> bool
  -> tables -> Uint63.t -> Uint63.t -> string option Marray.t -> string
  option Marray.t

val babelfish_impl :
  string Marray.t -> string Marray.t -> string Marray.t -> string option
  Marray.t

val babelfish :
  string Marray.t -> string Marray.t -> string Marray.t -> string option
  Marray.t
