
type comparison =
| Eq
| Lt
| Gt

val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val lor0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

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

val compare : string -> string -> comparison

type relkind =
| IsA
| HasA

val bdec : bool -> bool

type pstr = string

val hloop : pstr -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val hash : pstr -> Uint63.t

val walk : pstr -> pstr Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

type ht = { hkeys : pstr Marray.t; hnxt : Uint63.t Marray.t;
            hhead : Uint63.t Marray.t; hcnt : Uint63.t }

val lookup : ht -> pstr -> Uint63.t

val intern : ht -> pstr -> ht * Uint63.t

val iloop :
  pstr Marray.t -> pstr Marray.t -> Uint63.t -> Uint63.t -> ht -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> (ht * Uint63.t Marray.t) * Uint63.t
  Marray.t

val getbit : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val setbit :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val eloop :
  relkind Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val rowor :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t

val fw_inner :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t

val fw_outer :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val fill :
  (Uint63.t -> bool) -> Uint63.t -> Uint63.t -> bool Marray.t -> bool Marray.t

val answer :
  ht -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> pstr -> pstr -> relkind
  -> bool

val isahasa_impl :
  pstr Marray.t -> relkind Marray.t -> pstr Marray.t -> pstr Marray.t ->
  relkind Marray.t -> pstr Marray.t -> bool Marray.t

val isahasa :
  string Marray.t -> relkind Marray.t -> string Marray.t -> string Marray.t
  -> relkind Marray.t -> string Marray.t -> bool Marray.t
