
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

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

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

type uint = Uint63.t

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val splits : Uint63.t -> Uint63.t -> bool **)

let splits lo hi =
  (&&) (ltb lo hi) (ltb (Uint63.of_int (1)) (sub hi lo))

(** val midp : Uint63.t -> Uint63.t -> Uint63.t **)

let midp lo hi =
  add lo (div (sub hi lo) (Uint63.of_int (2)))

(** val merge_loop :
    sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec merge_loop key src mid hi i j k dst =
  if bdec (ltb k hi)
  then if ltb i mid
       then if leb hi j
            then merge_loop key src mid hi (add i (Uint63.of_int (1))) j
                   (add k (Uint63.of_int (1))) (set dst k (get src i))
            else if lesb (get key (get src i)) (get key (get src j))
                 then merge_loop key src mid hi (add i (Uint63.of_int (1))) j
                        (add k (Uint63.of_int (1))) (set dst k (get src i))
                 else merge_loop key src mid hi i (add j (Uint63.of_int (1)))
                        (add k (Uint63.of_int (1))) (set dst k (get src j))
       else merge_loop key src mid hi i (add j (Uint63.of_int (1)))
              (add k (Uint63.of_int (1))) (set dst k (get src j))
  else dst

(** val merge :
    sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let merge key src lo mid hi dst =
  merge_loop key src mid hi lo mid lo dst

(** val msort :
    sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort xs lo hi tgt oth =
  if bdec (splits lo hi)
  then let mid = midp lo hi in
       let (o1, t1) = msort xs lo mid oth tgt in
       let (o2, t2) = msort xs mid hi o1 t1 in
       ((merge xs o2 lo mid hi t2), o2)
  else ((set tgt lo lo), oth)

type res = (Uint63.t * Uint63.t) * Uint63.t

(** val bd : res -> Uint63.t **)

let bd =
  snd

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (-4611686018427387904))

(** val d2 :
    sint Marray.t -> sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let d2 xs ys a b =
  let dx = sub (get xs a) (get xs b) in
  let dy = sub (get ys a) (get ys b) in add (mul dx dx) (mul dy dy)

(** val near : sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let near xs xm b v =
  let dx = sub (get xs v) xm in ltb (mul dx dx) b

(** val strip_loop :
    sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t **)

let rec strip_loop xs xm b t hi k c o =
  if bdec (ltb k hi)
  then let v = get t k in
       if near xs xm b v
       then strip_loop xs xm b t hi (add k (Uint63.of_int (1)))
              (add c (Uint63.of_int (1))) (set o c v)
       else strip_loop xs xm b t hi (add k (Uint63.of_int (1))) c o
  else (o, c)

(** val inner_loop :
    sint Marray.t -> sint Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> res -> res **)

let rec inner_loop xs ys t e s t0 r =
  if bdec (ltb t0 e)
  then let a = get t s in
       let b = get t t0 in
       let dy = sub (get ys b) (get ys a) in
       if ltb (mul dy dy) (bd r)
       then let d = d2 xs ys a b in
            inner_loop xs ys t e s (add t0 (Uint63.of_int (1)))
              (if ltb d (bd r) then ((a, b), d) else r)
       else r
  else r

(** val outer_loop :
    sint Marray.t -> sint Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> res -> res **)

let rec outer_loop xs ys t e s r =
  if bdec (ltb s e)
  then outer_loop xs ys t e (add s (Uint63.of_int (1)))
         (inner_loop xs ys t e s (add s (Uint63.of_int (1))) r)
  else r

(** val solve :
    sint Marray.t -> sint Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t
    Marray.t * Uint63.t Marray.t) * res **)

let rec solve xs ys p lo hi tgt oth =
  if bdec (splits lo hi)
  then let mid = midp lo hi in
       let (p0, r1) = solve xs ys p lo mid oth tgt in
       let (o1, t1) = p0 in
       let (p1, r2) = solve xs ys p mid hi o1 t1 in
       let (o2, t2) = p1 in
       let t3 = merge ys o2 lo mid hi t2 in
       let r0 = if ltb (bd r2) (bd r1) then r2 else r1 in
       let (o3, e) = strip_loop xs (get xs (get p mid)) (bd r0) t3 hi lo lo o2
       in
       ((t3, o3), (outer_loop xs ys o3 e lo r0))
  else (((set tgt lo (get p lo)), oth), (((Uint63.of_int (0)),
         (Uint63.of_int (0))), iNF))

(** val closestpair_impl : sint Marray.t -> sint Marray.t -> uint * uint **)

let closestpair_impl xs ys =
  let n = length xs in
  let (p, a) =
    msort xs (Uint63.of_int (0)) n (make n (Uint63.of_int (0)))
      (make n (Uint63.of_int (0)))
  in
  let (_, r) =
    solve xs ys p (Uint63.of_int (0)) n a (make n (Uint63.of_int (0)))
  in
  fst r

(** val closestpair : sint Marray.t -> sint Marray.t -> uint * uint **)

let closestpair =
  closestpair_impl
