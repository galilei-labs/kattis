
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val nx : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let nx a b c r =
  mod0 (add (mul r a) b) c

(** val redraw :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    (Uint63.t * Uint63.t) * Uint63.t **)

let rec redraw n a b c r bud =
  if bdec (ltb (Uint63.of_int (0)) bud)
  then let r1 = nx a b c r in
       let r2 = nx a b c r1 in
       let x = mod0 r1 n in
       let y = mod0 r2 n in
       if eqb x y
       then redraw n a b c r2 (sub bud (Uint63.of_int (1)))
       else ((r2, x), y)
  else ((r, (Uint63.of_int (0))), (Uint63.of_int (0)))

(** val relabel :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec relabel nxt big q cnt rep =
  if bdec (ltb (Uint63.of_int (0)) cnt)
  then relabel nxt big (get nxt q) (sub cnt (Uint63.of_int (1)))
         (set rep q big)
  else rep

(** val merge :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> ((Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t Marray.t) * Uint63.t Marray.t **)

let merge big small rep nxt tl sz =
  let rep' = relabel nxt big small (get sz small) rep in
  let nxt' = set nxt (get tl big) small in
  let tl' = set tl big (get tl small) in
  let sz' = set sz big (add (get sz big) (get sz small)) in
  (((rep', nxt'), tl'), sz')

(** val union :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> ((Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t Marray.t) * Uint63.t Marray.t **)

let union x y rep nxt tl sz =
  let px = get rep x in
  let py = get rep y in
  if eqb px py
  then (((rep, nxt), tl), sz)
  else if ltb (get sz py) (get sz px)
       then merge px py rep nxt tl sz
       else merge py px rep nxt tl sz

(** val sim :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec sim n a b c r k rep nxt tl sz =
  if bdec (ltb (Uint63.of_int (0)) k)
  then let (p, y) = redraw n a b c r (add c (Uint63.of_int (1))) in
       let (r', x) = p in
       let (p0, sz') = union x y rep nxt tl sz in
       let (p1, tl') = p0 in
       let (rep', nxt') = p1 in
       sim n a b c r' (sub k (Uint63.of_int (1))) rep' nxt' tl' sz'
  else (rep, sz)

(** val init :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let rec init n i rep tl =
  if bdec (ltb i n)
  then init n (add i (Uint63.of_int (1))) (set rep i i) (set tl i i)
  else (rep, tl)

(** val tally :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t * Uint63.t
    Marray.t **)

let rec tally n i rep sz seen cnt g =
  if bdec (ltb i n)
  then let ro = get rep i in
       if eqb (get seen ro) (Uint63.of_int (0))
       then let s = get sz ro in
            tally n (add i (Uint63.of_int (1))) rep sz
              (set seen ro (Uint63.of_int (1)))
              (set cnt s (add (get cnt s) (Uint63.of_int (1))))
              (add g (Uint63.of_int (1)))
       else tally n (add i (Uint63.of_int (1))) rep sz seen cnt g
  else (g, cnt)

(** val countd :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let rec countd n i cnt d =
  if bdec (ltb i n)
  then countd n (add i (Uint63.of_int (1))) cnt
         (if ltb (Uint63.of_int (0)) (get cnt (sub n i))
          then add d (Uint63.of_int (1))
          else d)
  else d

(** val fill :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    (Uint63.t * Uint63.t) Marray.t -> (Uint63.t * Uint63.t) Marray.t **)

let rec fill n i j cnt out =
  if bdec (ltb i n)
  then let s = sub n i in
       let v = get cnt s in
       if ltb (Uint63.of_int (0)) v
       then fill n (add i (Uint63.of_int (1))) (add j (Uint63.of_int (1)))
              cnt (set out j (s, v))
       else fill n (add i (Uint63.of_int (1))) j cnt out
  else out

(** val chatter_impl :
    uint -> uint -> uint -> uint -> uint -> uint * (uint * uint) Marray.t **)

let chatter_impl n r a b c =
  let (rep0, tl0) =
    init n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (make n (Uint63.of_int (0)))
  in
  let (rep, sz) =
    sim n a b c r n rep0 (make n (Uint63.of_int (0))) tl0
      (make n (Uint63.of_int (1)))
  in
  let (g, cnt) =
    tally n (Uint63.of_int (0)) rep sz (make n (Uint63.of_int (0)))
      (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))
      (Uint63.of_int (0))
  in
  let d = countd n (Uint63.of_int (0)) cnt (Uint63.of_int (0)) in
  (g,
  (fill n (Uint63.of_int (0)) (Uint63.of_int (0)) cnt
    (make d ((Uint63.of_int (0)), (Uint63.of_int (0))))))

(** val chatter :
    uint -> uint -> uint -> uint -> uint -> uint * (uint * uint) Marray.t **)

let chatter =
  chatter_impl
