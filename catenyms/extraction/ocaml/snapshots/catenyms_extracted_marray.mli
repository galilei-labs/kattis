
val negb : bool -> bool

type comparison =
| Eq
| Lt
| Gt

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

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

val make0 : Uint63.t -> char63 -> string

val length0 : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

val compare : string -> string -> comparison

val bdec : bool -> bool

val splitc : Uint63.t -> Uint63.t -> bool

val midp : Uint63.t -> Uint63.t -> Uint63.t

val init_loop : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val cmpw : string Marray.t -> Uint63.t -> Uint63.t -> bool

val merge_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val copy_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val msort :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val fst_ch : string -> Uint63.t

val lst_ch : string -> Uint63.t

val build_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val deg_loop :
  string Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val chk_loop :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> bool -> ((Uint63.t * Uint63.t) * Uint63.t) * bool

val hier_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> string Marray.t ->
  Uint63.t -> string Marray.t * Uint63.t

val catenyms_impl : string Marray.t -> string Marray.t option

val catenyms : string Marray.t -> string Marray.t option
