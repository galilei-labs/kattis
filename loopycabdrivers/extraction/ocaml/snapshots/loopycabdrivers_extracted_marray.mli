
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val land0 : Uint63.t -> Uint63.t -> Uint63.t

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

val copy : 'a1 Marray.t -> 'a1 Marray.t

type char63 = Uint63.t

type string = Pstring.t

val make0 : Uint63.t -> char63 -> string

val length0 : string -> Uint63.t

val get0 : string -> Uint63.t -> char63

val compare : string -> string -> comparison

val bdec : bool -> bool

val hloop : string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val hmask : Uint63.t

val hsize : Uint63.t

val hash : string -> Uint63.t

val probe :
  Uint63.t Marray.t -> string Marray.t -> string -> Uint63.t -> Uint63.t ->
  Uint63.t * bool

type hstate = { ht : Uint63.t Marray.t; hn : string Marray.t; hc : Uint63.t }

val lookup : hstate -> string -> hstate * Uint63.t

val idloop :
  string Marray.t -> string Marray.t -> Uint63.t -> Uint63.t -> hstate ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> (hstate * Uint63.t
  Marray.t) * Uint63.t Marray.t

val cnt_loop :
  (Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t

val pre_loop :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val fill_loop :
  (Uint63.t -> Uint63.t) -> (Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val csr :
  Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t) -> (Uint63.t -> Uint63.t) ->
  Uint63.t Marray.t * Uint63.t Marray.t

val scan :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

type d1 = { mk : Uint63.t Marray.t; sv : Uint63.t Marray.t;
            sc : Uint63.t Marray.t; po : Uint63.t Marray.t; sp : Uint63.t;
            np : Uint63.t; rt : Uint63.t }

val dfs_step :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d1 -> d1 option

val dfs :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d1 -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t

val push_preds :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t

type d2 = { lb : Uint63.t Marray.t; sk : Uint63.t Marray.t; sq : Uint63.t;
            ii : Uint63.t; cc : Uint63.t }

val asg_step :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d2 -> d2
  option

val assign :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d2 ->
  Uint63.t -> Uint63.t -> d2

val merge_loop :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val copy_back :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val msort :
  (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val iota_loop : Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

type d3 = { gord : Uint63.t Marray.t; gn : Uint63.t; av : string Marray.t;
            an : Uint63.t }

val emit_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> d3 -> d3

val copy_loop :
  string Marray.t -> Uint63.t -> Uint63.t -> string Marray.t -> string
  Marray.t

val inner_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  string Marray.t -> string Marray.t

val group_arr :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  string Marray.t

val groups_loop :
  string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> string Marray.t Marray.t -> string
  Marray.t Marray.t

val name_le : string Marray.t -> Uint63.t -> Uint63.t -> bool

val empty_str : string

val loopy_impl :
  string Marray.t -> string Marray.t -> string Marray.t Marray.t * string
  Marray.t

val loopy_regions :
  string Marray.t -> string Marray.t -> string Marray.t Marray.t * string
  Marray.t
