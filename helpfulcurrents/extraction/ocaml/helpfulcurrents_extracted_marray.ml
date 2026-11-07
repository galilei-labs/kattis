
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

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

type char63 = Uint63.t

type string = Pstring.t

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val p : Uint63.t **)

let p =
  (Uint63.of_int (1000003))

(** val addm : Uint63.t -> Uint63.t -> Uint63.t **)

let addm a b =
  let s = add a b in if ltb s p then s else sub s p

(** val orf : Uint63.t -> Uint63.t -> Uint63.t **)

let orf a b =
  if eqb a (Uint63.of_int (0)) then b else a

(** val pass1 :
    string -> string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec pass1 s sb ym xm xim y x wv wf cv cf =
  if bdec (ltb x xm)
  then let c = get0 s x in
       let st = (&&) (eqb (add y (Uint63.of_int (1))) ym) (eqb x xim) in
       let sv = if st then (Uint63.of_int (1)) else (Uint63.of_int (0)) in
       let north =
         (&&)
           ((&&) (ltb (add y (Uint63.of_int (1))) ym)
             (negb (eqb (get0 sb x) (Uint63.of_int (64)))))
           (negb (eqb c (Uint63.of_int (35))))
       in
       let nv = if north then get cv x else (Uint63.of_int (0)) in
       let nf = if north then get cf x else (Uint63.of_int (0)) in
       let av = addm (addm sv nv) wv in
       let af = orf (orf sv nf) wf in
       let w = eqb c (Uint63.of_int (62)) in
       pass1 s sb ym xm xim y (add x (Uint63.of_int (1)))
         (if w then av else (Uint63.of_int (0)))
         (if w then af else (Uint63.of_int (0))) (set cv x av) (set cf x af)
  else (cv, cf)

(** val pass2 :
    string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> (Uint63.t
    Marray.t * Uint63.t Marray.t) * (Uint63.t * Uint63.t) **)

let rec pass2 s x ev ef cv cf av af =
  if bdec (ltb (Uint63.of_int (0)) x)
  then let x' = sub x (Uint63.of_int (1)) in
       let c = get0 s x' in
       let bv = addm (get cv x') ev in
       let bf = orf (get cf x') ef in
       let e = eqb c (Uint63.of_int (60)) in
       let k = eqb c (Uint63.of_int (64)) in
       pass2 s x' (if e then bv else (Uint63.of_int (0)))
         (if e then bf else (Uint63.of_int (0))) (set cv x' bv)
         (set cf x' bf) (if k then bv else av) (if k then bf else af)
  else ((cv, cf), (av, af))

(** val rows :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec rows m ym xm xim k cv cf av af =
  if bdec (ltb (Uint63.of_int (0)) k)
  then let y = sub k (Uint63.of_int (1)) in
       let s = get m y in
       let r1 =
         pass1 s (get m k) ym xm xim y (Uint63.of_int (0))
           (Uint63.of_int (0)) (Uint63.of_int (0)) cv cf
       in
       let r2 =
         pass2 s xm (Uint63.of_int (0)) (Uint63.of_int (0)) (fst r1) 
           (snd r1) av af
       in
       rows m ym xm xim y (fst (fst r2)) (snd (fst r2)) (fst (snd r2))
         (snd (snd r2))
  else (av, af)

(** val helpfulcurrents_impl :
    uint -> uint -> uint -> string Marray.t -> uint option **)

let helpfulcurrents_impl ym xm xim m =
  let r =
    rows m ym xm xim ym (make xm (Uint63.of_int (0)))
      (make xm (Uint63.of_int (0))) (Uint63.of_int (0)) (Uint63.of_int (0))
  in
  if eqb (snd r) (Uint63.of_int (0)) then None else Some (fst r)

module HelpfulcurrentsImpl =
 struct
  (** val helpfulcurrents :
      uint -> uint -> uint -> string Marray.t -> uint option **)

  let helpfulcurrents =
    helpfulcurrents_impl
 end
