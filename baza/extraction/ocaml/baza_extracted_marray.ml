
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type char63 = Uint63.t

type string = Pstring.t

(** val length0 : string -> Uint63.t **)

let length0 = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

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

(** val sel : tab -> Uint63.t -> Uint63.t Marray.t **)

let sel t c =
  if ltb c (Uint63.of_int (13))
  then if ltb c (Uint63.of_int (6))
       then if ltb c (Uint63.of_int (3))
            then if ltb c (Uint63.of_int (1))
                 then t.tc0
                 else if ltb c (Uint63.of_int (2)) then t.tc1 else t.tc2
            else if ltb c (Uint63.of_int (4))
                 then t.tc3
                 else if ltb c (Uint63.of_int (5)) then t.tc4 else t.tc5
       else if ltb c (Uint63.of_int (9))
            then if ltb c (Uint63.of_int (7))
                 then t.tc6
                 else if ltb c (Uint63.of_int (8)) then t.tc7 else t.tc8
            else if ltb c (Uint63.of_int (11))
                 then if ltb c (Uint63.of_int (10)) then t.tc9 else t.tc10
                 else if ltb c (Uint63.of_int (12)) then t.tc11 else t.tc12
  else if ltb c (Uint63.of_int (19))
       then if ltb c (Uint63.of_int (16))
            then if ltb c (Uint63.of_int (14))
                 then t.tc13
                 else if ltb c (Uint63.of_int (15)) then t.tc14 else t.tc15
            else if ltb c (Uint63.of_int (17))
                 then t.tc16
                 else if ltb c (Uint63.of_int (18)) then t.tc17 else t.tc18
       else if ltb c (Uint63.of_int (22))
            then if ltb c (Uint63.of_int (20))
                 then t.tc19
                 else if ltb c (Uint63.of_int (21)) then t.tc20 else t.tc21
            else if ltb c (Uint63.of_int (24))
                 then if ltb c (Uint63.of_int (23)) then t.tc22 else t.tc23
                 else if ltb c (Uint63.of_int (25)) then t.tc24 else t.tc25

(** val upd : tab -> Uint63.t -> Uint63.t Marray.t -> tab **)

let upd t c a =
  if ltb c (Uint63.of_int (13))
  then if ltb c (Uint63.of_int (6))
       then if ltb c (Uint63.of_int (3))
            then if ltb c (Uint63.of_int (1))
                 then { tc0 = a; tc1 = t.tc1; tc2 = t.tc2; tc3 = t.tc3; tc4 =
                        t.tc4; tc5 = t.tc5; tc6 = t.tc6; tc7 = t.tc7; tc8 =
                        t.tc8; tc9 = t.tc9; tc10 = t.tc10; tc11 = t.tc11;
                        tc12 = t.tc12; tc13 = t.tc13; tc14 = t.tc14; tc15 =
                        t.tc15; tc16 = t.tc16; tc17 = t.tc17; tc18 = t.tc18;
                        tc19 = t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                        t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                 else if ltb c (Uint63.of_int (2))
                      then { tc0 = t.tc0; tc1 = a; tc2 = t.tc2; tc3 = t.tc3;
                             tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6; tc7 =
                             t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 = t.tc10;
                             tc11 = t.tc11; tc12 = t.tc12; tc13 = t.tc13;
                             tc14 = t.tc14; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = a; tc3 = t.tc3;
                             tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6; tc7 =
                             t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 = t.tc10;
                             tc11 = t.tc11; tc12 = t.tc12; tc13 = t.tc13;
                             tc14 = t.tc14; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
            else if ltb c (Uint63.of_int (4))
                 then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 = a; tc4 =
                        t.tc4; tc5 = t.tc5; tc6 = t.tc6; tc7 = t.tc7; tc8 =
                        t.tc8; tc9 = t.tc9; tc10 = t.tc10; tc11 = t.tc11;
                        tc12 = t.tc12; tc13 = t.tc13; tc14 = t.tc14; tc15 =
                        t.tc15; tc16 = t.tc16; tc17 = t.tc17; tc18 = t.tc18;
                        tc19 = t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                        t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                 else if ltb c (Uint63.of_int (5))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = a; tc5 = t.tc5; tc6 = t.tc6; tc7 =
                             t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 = t.tc10;
                             tc11 = t.tc11; tc12 = t.tc12; tc13 = t.tc13;
                             tc14 = t.tc14; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = a; tc6 = t.tc6; tc7 =
                             t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 = t.tc10;
                             tc11 = t.tc11; tc12 = t.tc12; tc13 = t.tc13;
                             tc14 = t.tc14; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
       else if ltb c (Uint63.of_int (9))
            then if ltb c (Uint63.of_int (7))
                 then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 = t.tc3;
                        tc4 = t.tc4; tc5 = t.tc5; tc6 = a; tc7 = t.tc7; tc8 =
                        t.tc8; tc9 = t.tc9; tc10 = t.tc10; tc11 = t.tc11;
                        tc12 = t.tc12; tc13 = t.tc13; tc14 = t.tc14; tc15 =
                        t.tc15; tc16 = t.tc16; tc17 = t.tc17; tc18 = t.tc18;
                        tc19 = t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                        t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                 else if ltb c (Uint63.of_int (8))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = a; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                             t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 =
                             t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = a; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                             t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 =
                             t.tc25 }
            else if ltb c (Uint63.of_int (11))
                 then if ltb c (Uint63.of_int (10))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = a; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                             t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 =
                             t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 = a;
                             tc11 = t.tc11; tc12 = t.tc12; tc13 = t.tc13;
                             tc14 = t.tc14; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                 else if ltb c (Uint63.of_int (12))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = a; tc12 = t.tc12; tc13 = t.tc13;
                             tc14 = t.tc14; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = a; tc13 = t.tc13;
                             tc14 = t.tc14; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
  else if ltb c (Uint63.of_int (19))
       then if ltb c (Uint63.of_int (16))
            then if ltb c (Uint63.of_int (14))
                 then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 = t.tc3;
                        tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6; tc7 = t.tc7;
                        tc8 = t.tc8; tc9 = t.tc9; tc10 = t.tc10; tc11 =
                        t.tc11; tc12 = t.tc12; tc13 = a; tc14 = t.tc14;
                        tc15 = t.tc15; tc16 = t.tc16; tc17 = t.tc17; tc18 =
                        t.tc18; tc19 = t.tc19; tc20 = t.tc20; tc21 = t.tc21;
                        tc22 = t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 =
                        t.tc25 }
                 else if ltb c (Uint63.of_int (15))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = a; tc15 = t.tc15; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = a; tc16 = t.tc16;
                             tc17 = t.tc17; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
            else if ltb c (Uint63.of_int (17))
                 then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 = t.tc3;
                        tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6; tc7 = t.tc7;
                        tc8 = t.tc8; tc9 = t.tc9; tc10 = t.tc10; tc11 =
                        t.tc11; tc12 = t.tc12; tc13 = t.tc13; tc14 = t.tc14;
                        tc15 = t.tc15; tc16 = a; tc17 = t.tc17; tc18 =
                        t.tc18; tc19 = t.tc19; tc20 = t.tc20; tc21 = t.tc21;
                        tc22 = t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 =
                        t.tc25 }
                 else if ltb c (Uint63.of_int (18))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = a; tc18 = t.tc18; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = a; tc19 = t.tc19;
                             tc20 = t.tc20; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
       else if ltb c (Uint63.of_int (22))
            then if ltb c (Uint63.of_int (20))
                 then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 = t.tc3;
                        tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6; tc7 = t.tc7;
                        tc8 = t.tc8; tc9 = t.tc9; tc10 = t.tc10; tc11 =
                        t.tc11; tc12 = t.tc12; tc13 = t.tc13; tc14 = t.tc14;
                        tc15 = t.tc15; tc16 = t.tc16; tc17 = t.tc17; tc18 =
                        t.tc18; tc19 = a; tc20 = t.tc20; tc21 = t.tc21;
                        tc22 = t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 =
                        t.tc25 }
                 else if ltb c (Uint63.of_int (21))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = a; tc21 = t.tc21; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = a; tc22 = t.tc22;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
            else if ltb c (Uint63.of_int (24))
                 then if ltb c (Uint63.of_int (23))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 = a;
                             tc23 = t.tc23; tc24 = t.tc24; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                             t.tc22; tc23 = a; tc24 = t.tc24; tc25 = t.tc25 }
                 else if ltb c (Uint63.of_int (25))
                      then { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                             t.tc22; tc23 = t.tc23; tc24 = a; tc25 = t.tc25 }
                      else { tc0 = t.tc0; tc1 = t.tc1; tc2 = t.tc2; tc3 =
                             t.tc3; tc4 = t.tc4; tc5 = t.tc5; tc6 = t.tc6;
                             tc7 = t.tc7; tc8 = t.tc8; tc9 = t.tc9; tc10 =
                             t.tc10; tc11 = t.tc11; tc12 = t.tc12; tc13 =
                             t.tc13; tc14 = t.tc14; tc15 = t.tc15; tc16 =
                             t.tc16; tc17 = t.tc17; tc18 = t.tc18; tc19 =
                             t.tc19; tc20 = t.tc20; tc21 = t.tc21; tc22 =
                             t.tc22; tc23 = t.tc23; tc24 = t.tc24; tc25 = a }

(** val mk_tab : Uint63.t -> tab **)

let mk_tab cap =
  { tc0 = (make cap (Uint63.of_int (0))); tc1 =
    (make cap (Uint63.of_int (0))); tc2 = (make cap (Uint63.of_int (0)));
    tc3 = (make cap (Uint63.of_int (0))); tc4 =
    (make cap (Uint63.of_int (0))); tc5 = (make cap (Uint63.of_int (0)));
    tc6 = (make cap (Uint63.of_int (0))); tc7 =
    (make cap (Uint63.of_int (0))); tc8 = (make cap (Uint63.of_int (0)));
    tc9 = (make cap (Uint63.of_int (0))); tc10 =
    (make cap (Uint63.of_int (0))); tc11 = (make cap (Uint63.of_int (0)));
    tc12 = (make cap (Uint63.of_int (0))); tc13 =
    (make cap (Uint63.of_int (0))); tc14 = (make cap (Uint63.of_int (0)));
    tc15 = (make cap (Uint63.of_int (0))); tc16 =
    (make cap (Uint63.of_int (0))); tc17 = (make cap (Uint63.of_int (0)));
    tc18 = (make cap (Uint63.of_int (0))); tc19 =
    (make cap (Uint63.of_int (0))); tc20 = (make cap (Uint63.of_int (0)));
    tc21 = (make cap (Uint63.of_int (0))); tc22 =
    (make cap (Uint63.of_int (0))); tc23 = (make cap (Uint63.of_int (0)));
    tc24 = (make cap (Uint63.of_int (0))); tc25 =
    (make cap (Uint63.of_int (0))) }

(** val tget : tab -> Uint63.t -> Uint63.t -> Uint63.t **)

let tget t c n =
  get (sel t c) n

(** val tset : tab -> Uint63.t -> Uint63.t -> Uint63.t -> tab **)

let tset t c n v =
  upd t c (set (sel t c) n v)

type ires = { r_T : tab; r_cnt : Uint63.t Marray.t; r_sz : Uint63.t;
              r_n : Uint63.t; r_s : Uint63.t }

(** val ins_loop :
    string -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> ires **)

let rec ins_loop w l t cnt sz i n s =
  if bdec (ltb i l)
  then let c = sub (get0 w i) (Uint63.of_int (97)) in
       let m = tget t c n in
       if eqb m (Uint63.of_int (0))
       then ins_loop w l (tset t c n sz) (set cnt sz (Uint63.of_int (1)))
              (add sz (Uint63.of_int (1))) (add i (Uint63.of_int (1))) sz
              (add s (Uint63.of_int (1)))
       else let k = add (get cnt m) (Uint63.of_int (1)) in
            ins_loop w l t (set cnt m k) sz (add i (Uint63.of_int (1))) m
              (add s k)
  else { r_T = t; r_cnt = cnt; r_sz = sz; r_n = n; r_s = s }

type bres = { b_T : tab; b_cnt : Uint63.t Marray.t; b_end : Uint63.t Marray.t }

(** val build :
    string Marray.t -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> bres **)

let rec build db n t cnt endv sz j =
  if bdec (ltb j n)
  then let w = get db j in
       let r =
         ins_loop w (length0 w) t cnt sz (Uint63.of_int (0))
           (Uint63.of_int (0)) (Uint63.of_int (0))
       in
       build db n r.r_T r.r_cnt
         (set endv r.r_n (add (add j (Uint63.of_int (1))) r.r_s)) r.r_sz
         (add j (Uint63.of_int (1)))
  else { b_T = t; b_cnt = cnt; b_end = endv }

(** val qwalk :
    string -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec qwalk q l t cnt endv n i n0 s =
  if bdec (ltb i l)
  then let m = tget t (sub (get0 q i) (Uint63.of_int (97))) n0 in
       if eqb m (Uint63.of_int (0))
       then add n s
       else qwalk q l t cnt endv n (add i (Uint63.of_int (1))) m
              (add s (get cnt m))
  else let e = get endv n0 in if eqb e (Uint63.of_int (0)) then add n s else e

(** val query :
    string -> tab -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t **)

let query q t cnt endv n =
  qwalk q (length0 q) t cnt endv n (Uint63.of_int (0)) (Uint63.of_int (0))
    (Uint63.of_int (0))

(** val answer :
    string Marray.t -> Uint63.t -> tab -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let rec answer qs q t cnt endv n out k =
  if bdec (ltb k q)
  then answer qs q t cnt endv n (set out k (query (get qs k) t cnt endv n))
         (add k (Uint63.of_int (1)))
  else out

(** val total :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec total db n j acc =
  if bdec (ltb j n)
  then total db n (add j (Uint63.of_int (1))) (add acc (length0 (get db j)))
  else acc

(** val baza_impl : string Marray.t -> string Marray.t -> uint Marray.t **)

let baza_impl db qs =
  let n = length db in
  let cap =
    add (Uint63.of_int (1))
      (total db n (Uint63.of_int (0)) (Uint63.of_int (0)))
  in
  let b =
    build db n (mk_tab cap) (make cap (Uint63.of_int (0)))
      (make cap (Uint63.of_int (0))) (Uint63.of_int (1)) (Uint63.of_int (0))
  in
  let q = length qs in
  answer qs q b.b_T b.b_cnt b.b_end n (make q (Uint63.of_int (0)))
    (Uint63.of_int (0))

module BazaImpl =
 struct
  (** val baza : string Marray.t -> string Marray.t -> uint Marray.t **)

  let baza =
    baza_impl
 end
