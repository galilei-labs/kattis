
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val lesb : Uint63.t -> Uint63.t -> bool **)

let lesb = Uint63.les

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type sint = Uint63.t

type big = { b0 : Uint63.t Marray.t; b1 : Uint63.t Marray.t;
             b2 : Uint63.t Marray.t; b3 : Uint63.t Marray.t }

(** val chunk : big -> Uint63.t -> Uint63.t Marray.t **)

let chunk b q =
  if eqb q (Uint63.of_int (0))
  then b.b0
  else if eqb q (Uint63.of_int (1))
       then b.b1
       else if eqb q (Uint63.of_int (2)) then b.b2 else b.b3

(** val upd : big -> Uint63.t -> Uint63.t Marray.t -> big **)

let upd b q a =
  if eqb q (Uint63.of_int (0))
  then { b0 = a; b1 = b.b1; b2 = b.b2; b3 = b.b3 }
  else if eqb q (Uint63.of_int (1))
       then { b0 = b.b0; b1 = a; b2 = b.b2; b3 = b.b3 }
       else if eqb q (Uint63.of_int (2))
            then { b0 = b.b0; b1 = b.b1; b2 = a; b3 = b.b3 }
            else { b0 = b.b0; b1 = b.b1; b2 = b.b2; b3 = a }

(** val bget : big -> Uint63.t -> Uint63.t **)

let bget b k =
  let q = lsr0 k (Uint63.of_int (21)) in
  get (chunk b q) (sub k (lsl0 q (Uint63.of_int (21))))

(** val bset : big -> Uint63.t -> Uint63.t -> big **)

let bset b k v =
  let q = lsr0 k (Uint63.of_int (21)) in
  upd b q (set (chunk b q) (sub k (lsl0 q (Uint63.of_int (21)))) v)

(** val clen : Uint63.t -> Uint63.t -> Uint63.t **)

let clen cap q =
  let lo = lsl0 q (Uint63.of_int (21)) in
  if leb cap lo
  then (Uint63.of_int (0))
  else if leb (sub cap lo) (Uint63.of_int (2097152))
       then sub cap lo
       else (Uint63.of_int (2097152))

(** val bmake : Uint63.t -> Uint63.t -> big **)

let bmake cap v =
  { b0 = (make (clen cap (Uint63.of_int (0))) v); b1 =
    (make (clen cap (Uint63.of_int (1))) v); b2 =
    (make (clen cap (Uint63.of_int (2))) v); b3 =
    (make (clen cap (Uint63.of_int (3))) v) }

(** val hA : Uint63.t **)

let hA =
  (Uint63.of_int (2177342782468422677))

(** val hash : Uint63.t -> Uint63.t -> Uint63.t **)

let hash cap s =
  lsr0 (mul (lsr0 (mul s hA) (Uint63.of_int (40))) cap) (Uint63.of_int (23))

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val code : Uint63.t -> Uint63.t -> Uint63.t **)

let code i j =
  add (lsl0 i (Uint63.of_int (12))) j

(** val chk :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> bool **)

let chk x n k l t c =
  let i = lsr0 c (Uint63.of_int (12)) in
  let j = sub c (lsl0 i (Uint63.of_int (12))) in
  (&&)
    ((&&)
      ((&&)
        ((&&)
          ((&&) ((&&) ((&&) (ltb i n) (ltb j n)) (negb (eqb i j)))
            (negb (eqb i k)))
          (negb (eqb i l)))
        (negb (eqb j k)))
      (negb (eqb j l)))
    (eqb (add (get x i) (get x j)) t)

(** val walk :
    Uint63.t Marray.t -> big -> big -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let rec walk x nx cd n k l t e =
  if bdec (eqb e (Uint63.of_int (0)))
  then false
  else if chk x n k l t (bget cd e)
       then true
       else let e' = bget nx e in
            if bdec (ltb e' e) then walk x nx cd n k l t e' else false

type tbl = { th : big; tn : big; tc : big; tk : Uint63.t }

(** val ins :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> tbl -> tbl **)

let ins x cap i j t =
  let e = add t.tk (Uint63.of_int (1)) in
  let h = hash cap (add (get x i) (get x j)) in
  let old = bget t.th h in
  let nx = bset t.tn e old in
  let cd = bset t.tc e (code i j) in
  let hd = bset t.th h e in { th = hd; tn = nx; tc = cd; tk = e }

(** val build_in :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> tbl
    -> tbl **)

let rec build_in x cap n i j t =
  if bdec (ltb j n)
  then build_in x cap n i (add j (Uint63.of_int (1))) (ins x cap i j t)
  else t

(** val build_out :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> tbl -> tbl **)

let rec build_out x cap n i t =
  if bdec (ltb i n)
  then build_out x cap n (add i (Uint63.of_int (1)))
         (build_in x cap n i (add i (Uint63.of_int (1))) t)
  else t

(** val query :
    Uint63.t Marray.t -> tbl -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    -> bool **)

let query x t cap n k l =
  let t0 = sub (get x k) (get x l) in
  let e = bget t.th (hash cap t0) in walk x t.tn t.tc n k l t0 e

(** val any_l :
    Uint63.t Marray.t -> tbl -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    -> bool **)

let rec any_l x t cap n k l =
  if bdec (ltb l n)
  then if eqb l k
       then any_l x t cap n k (add l (Uint63.of_int (1)))
       else if query x t cap n k l
            then true
            else any_l x t cap n k (add l (Uint63.of_int (1)))
  else false

(** val best_k :
    Uint63.t Marray.t -> tbl -> Uint63.t -> Uint63.t -> Uint63.t -> bool ->
    Uint63.t -> Uint63.t option **)

let rec best_k x t cap n k found best =
  if bdec (ltb k n)
  then if (&&) found (lesb (get x k) best)
       then best_k x t cap n (add k (Uint63.of_int (1))) found best
       else if any_l x t cap n k (Uint63.of_int (0))
            then best_k x t cap n (add k (Uint63.of_int (1))) true (get x k)
            else best_k x t cap n (add k (Uint63.of_int (1))) found best
  else if found then Some best else None

(** val sumsets_impl : Uint63.t Marray.t -> Uint63.t option **)

let sumsets_impl x =
  let n = length x in
  let cap =
    add (lsr0 (mul n (sub n (Uint63.of_int (1)))) (Uint63.of_int (1)))
      (Uint63.of_int (1))
  in
  let t0 = { th = (bmake cap (Uint63.of_int (0))); tn =
    (bmake cap (Uint63.of_int (0))); tc = (bmake cap (Uint63.of_int (0)));
    tk = (Uint63.of_int (0)) }
  in
  let t = build_out x cap n (Uint63.of_int (0)) t0 in
  best_k x t cap n (Uint63.of_int (0)) false (Uint63.of_int (0))

(** val sumsets : sint Marray.t -> sint option **)

let sumsets =
  sumsets_impl
