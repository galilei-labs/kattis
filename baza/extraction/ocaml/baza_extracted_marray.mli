
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

type tab = { tc0 : Uint63.t Marray.t; tc1 : Uint63.t Marray.t;
             tc2 : Uint63.t Marray.t; tc3 : Uint63.t Marray.t;
             tc4 : Uint63.t Marray.t; tc5 : Uint63.t Marray.t;
             tc6 : Uint63.t Marray.t; tc7 : Uint63.t Marray.t;
             tc8 : Uint63.t Marray.t; tc9 : Uint63.t Marray.t;
             tc10 : Uint63.t Marray.t; tc11 : Uint63.t Marray.t;
             tc12 : Uint63.t Marray.t; tc13 : Uint63.t Marray.t;
             tc14 : Uint63.t Marray.t; tc15 : Uint63.t Marray.t;
             tc16 : Uint63.t Marray.t; tc17 : Uint63.t Marray.t;
             tc18 : Uint63.t Marray.t; tc19 : Uint63.t Marray.t;
             tc20 : Uint63.t Marray.t; tc21 : Uint63.t Marray.t;
             tc22 : Uint63.t Marray.t; tc23 : Uint63.t Marray.t;
             tc24 : Uint63.t Marray.t; tc25 : Uint63.t Marray.t }

val sel : tab -> Uint63.t -> Uint63.t Marray.t

val upd : tab -> Uint63.t -> Uint63.t Marray.t -> tab

val mk_tab : Uint63.t -> tab

val tget : tab -> Uint63.t -> Uint63.t -> Uint63.t

val tset : tab -> Uint63.t -> Uint63.t -> Uint63.t -> tab

type ires = { r_T : tab; r_cnt : Uint63.t Marray.t; r_sz : Uint63.t;
              r_n : Uint63.t; r_s : Uint63.t }

val ins_loop :
  string -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> ires

type bres = { b_T : tab; b_cnt : Uint63.t Marray.t; b_end : Uint63.t Marray.t }

val build :
  string Marray.t -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> bres

val qwalk :
  string -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val query :
  string -> tab -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t

val answer :
  string Marray.t -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val total : string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val baza_impl : string Marray.t -> string Marray.t -> uint Marray.t

val baza : string Marray.t -> string Marray.t -> uint Marray.t
