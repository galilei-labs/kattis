
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

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

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

(** val min_i : Uint63.t -> Uint63.t -> Uint63.t **)

let min_i a b =
  if ltb a b then a else b

(** val cross_m :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let cross_m x y a b c =
  let xa = get x a in
  let ya = get y a in
  sub (mul (sub (get x b) xa) (sub (get y c) ya))
    (mul (sub (get y b) ya) (sub (get x c) xa))

(** val le_pt :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool **)

let le_pt x y a b =
  let xa = get x a in
  let xb = get x b in
  if ltsb xa xb
  then true
  else if eqb xa xb then lesb (get y a) (get y b) else false

(** val take_left :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let take_left x y src mid hi i j =
  if ltb i mid
  then if ltb j hi then le_pt x y (get src i) (get src j) else true
  else false

(** val merge :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec merge x y src mid hi i j k dst =
  if bdec (ltb k hi)
  then if take_left x y src mid hi i j
       then merge x y src mid hi (add i (Uint63.of_int (1))) j
              (add k (Uint63.of_int (1))) (set dst k (get src i))
       else merge x y src mid hi i (add j (Uint63.of_int (1)))
              (add k (Uint63.of_int (1))) (set dst k (get src j))
  else dst

(** val pass :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec pass x y src w n lo dst =
  if bdec (ltb lo (min_i (add (add lo w) w) n))
  then pass x y src w n (min_i (add (add lo w) w) n)
         (merge x y src (min_i (add lo w) n) (min_i (add (add lo w) w) n) lo
           (min_i (add lo w) n) lo dst)
  else dst

(** val sortl :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec sortl x y n w src dst =
  if bdec ((&&) (ltb w n) (ltb w (add w w)))
  then sortl x y n (add w w) (pass x y src w n (Uint63.of_int (0)) dst) src
  else src

(** val initl :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec initl n i a =
  if bdec (ltb i n)
  then initl n (add i (Uint63.of_int (1))) (set a i i)
  else a

(** val msort :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let msort x y n =
  sortl x y n (Uint63.of_int (1))
    (initl n (Uint63.of_int (0)) (make n (Uint63.of_int (0))))
    (make n (Uint63.of_int (0)))

(** val pop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec pop x y st lim k q =
  if bdec
       ((&&) (ltb lim k)
         (lesb
           (cross_m x y (get st (sub k (Uint63.of_int (2))))
             (get st (sub k (Uint63.of_int (1)))) q)
           (Uint63.of_int (0))))
  then pop x y st lim (sub k (Uint63.of_int (1))) q
  else k

(** val lower :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t **)

let rec lower x y ord st n k i =
  if bdec (ltb i n)
  then let q = get ord i in
       let k' = pop x y st (Uint63.of_int (1)) k q in
       lower x y ord (set st k' q) n (add k' (Uint63.of_int (1)))
         (add i (Uint63.of_int (1)))
  else (st, k)

(** val upper :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t **)

let rec upper x y ord st lim k j =
  if bdec (ltb (Uint63.of_int (0)) j)
  then let q = get ord (sub j (Uint63.of_int (1))) in
       let k' = pop x y st lim k q in
       upper x y ord (set st k' q) lim (add k' (Uint63.of_int (1)))
         (sub j (Uint63.of_int (1)))
  else (st, k)

(** val copyl :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copyl src dst h i =
  if bdec (ltb i h)
  then copyl src (set dst i (get src i)) h (add i (Uint63.of_int (1)))
  else dst

(** val hull : sint Marray.t -> sint Marray.t -> uint Marray.t **)

let hull x y =
  let n = length x in
  let ord = msort x y n in
  let a = get ord (Uint63.of_int (0)) in
  let b = get ord (sub n (Uint63.of_int (1))) in
  if (&&) (eqb (get x a) (get x b)) (eqb (get y a) (get y b))
  then make (Uint63.of_int (1)) a
  else let (st1, l) =
         lower x y ord
           (set (make (add n n) (Uint63.of_int (0))) (Uint63.of_int (0)) a) n
           (Uint63.of_int (1)) (Uint63.of_int (1))
       in
       let (st2, k) = upper x y ord st1 l l (sub n (Uint63.of_int (1))) in
       copyl st2 (make (sub k (Uint63.of_int (1))) (Uint63.of_int (0)))
         (sub k (Uint63.of_int (1))) (Uint63.of_int (0))

(** val convex_hull : sint Marray.t -> sint Marray.t -> uint Marray.t **)

let convex_hull =
  hull
