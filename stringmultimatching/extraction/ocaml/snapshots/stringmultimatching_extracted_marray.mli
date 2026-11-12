
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type char63 = Uint63.t

type string = Pstring.t

val length0 : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

type uint = Uint63.t

val bdec : bool -> bool

type trie = { tchr : Uint63.t Marray.t; tpar : Uint63.t Marray.t;
              tfc : Uint63.t Marray.t; tns : Uint63.t Marray.t;
              tdep : Uint63.t Marray.t; tn : Uint63.t }

val lookup_from :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val lookup : trie -> Uint63.t -> Uint63.t -> Uint63.t

val add_child : trie -> Uint63.t -> Uint63.t -> trie * Uint63.t

type bstate = { bact : Uint63.t Marray.t; bcur : Uint63.t Marray.t;
                bw : Uint63.t; bt : trie }

val round_loop :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bstate -> bstate

val rounds : string Marray.t -> Uint63.t -> Uint63.t -> bstate -> bstate

val sums :
  string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t * Uint63.t

val iota : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val plist_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val walk : trie -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val fail_loop :
  trie -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t

val emit_list :
  ('a1 -> Uint63.t -> Uint63.t -> 'a1) -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> 'a1 -> 'a1

val emit_chain :
  ('a1 -> Uint63.t -> Uint63.t -> 'a1) -> trie -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val scan :
  ('a1 -> Uint63.t -> Uint63.t -> 'a1) -> trie -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> string ->
  Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val f_cnt : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val f_fill :
  (Uint63.t Marray.t Marray.t * Uint63.t Marray.t) -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t Marray.t * Uint63.t Marray.t

val alloc_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t Marray.t ->
  Uint63.t Marray.t Marray.t

val multimatch_impl : string Marray.t -> string -> uint Marray.t Marray.t

val multimatch : string Marray.t -> string -> uint Marray.t Marray.t
