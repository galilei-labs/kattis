
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

type char63 = Uint63.t

type string = Pstring.t

val length : string -> Uint63.t

val get : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

val init_rank :
  string -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array

val init_id : Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array

val skey : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val cbound : Uint63.t -> Uint63.t

val count_loop :
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t ->
  Uint63.t array -> Uint63.t array

val prefix_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array

val place_loop :
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t ->
  Uint63.t array -> Uint63.t array -> Uint63.t array

val csort :
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array
  -> Uint63.t array

val rank_loop :
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t ->
  Uint63.t -> Uint63.t array -> Uint63.t array * Uint63.t

val rounds :
  Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array
  -> Uint63.t array -> Uint63.t array

val suffix_array_impl : string -> uint array

val suffix_array : string -> uint array
