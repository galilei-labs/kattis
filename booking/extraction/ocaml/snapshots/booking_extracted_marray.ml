
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

type 'a datetime = { year : 'a; month : 'a; day : 'a; hour : 'a; minute : 'a }

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val swap :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let swap a i j =
  let x = get a i in let y = get a j in set (set a i y) j x

(** val part_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t **)

let rec part_loop a p hi1 i j =
  if bdec (ltb j hi1)
  then if ltb (get a j) p
       then part_loop (swap a i j) p hi1 (add i (Uint63.of_int (1)))
              (add j (Uint63.of_int (1)))
       else part_loop a p hi1 i (add j (Uint63.of_int (1)))
  else (a, i)

(** val partition :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t **)

let partition a lo hi =
  let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
  let hi1 = sub hi (Uint63.of_int (1)) in
  let a1 = swap a mid hi1 in
  let p = get a1 hi1 in
  let (a2, i) = part_loop a1 p hi1 lo lo in ((swap a2 i hi1), i)

(** val qsort :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec qsort a lo hi =
  if bdec (ltb (add lo (Uint63.of_int (1))) hi)
  then let (a1, m) = partition a lo hi in
       if bdec ((&&) (leb lo m) (ltb m hi))
       then let a2 = qsort a1 lo m in qsort a2 (add m (Uint63.of_int (1))) hi
       else a1
  else a

(** val sort_all : Uint63.t Marray.t -> Uint63.t Marray.t **)

let sort_all a =
  qsort a (Uint63.of_int (0)) (length a)

(** val sweep :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t **)

let rec sweep a r n p q best =
  if bdec (ltb p n)
  then if bdec ((&&) (ltb q n) (leb (get r q) (get a p)))
       then sweep a r n p (add q (Uint63.of_int (1))) best
       else sweep a r n (add p (Uint63.of_int (1))) q
              (if ltb (add best q) (add p (Uint63.of_int (1)))
               then sub (add p (Uint63.of_int (1))) q
               else best)
  else best

(** val leapb : Uint63.t -> bool **)

let leapb y =
  (||)
    ((&&) (eqb (mod0 y (Uint63.of_int (4))) (Uint63.of_int (0)))
      (negb (eqb (mod0 y (Uint63.of_int (100))) (Uint63.of_int (0)))))
    (eqb (mod0 y (Uint63.of_int (400))) (Uint63.of_int (0)))

(** val days_before_year : Uint63.t -> Uint63.t **)

let days_before_year y =
  add
    (sub
      (add (mul (Uint63.of_int (365)) y)
        (div (add y (Uint63.of_int (3))) (Uint63.of_int (4))))
      (div (add y (Uint63.of_int (99))) (Uint63.of_int (100))))
    (div (add y (Uint63.of_int (399))) (Uint63.of_int (400)))

(** val days_before_month : Uint63.t -> Uint63.t -> Uint63.t **)

let days_before_month y m =
  sub
    (div (sub (mul (Uint63.of_int (367)) m) (Uint63.of_int (362)))
      (Uint63.of_int (12)))
    (if leb m (Uint63.of_int (2))
     then (Uint63.of_int (0))
     else if leapb y then (Uint63.of_int (1)) else (Uint63.of_int (2)))

(** val mach_minutes : uint datetime -> Uint63.t **)

let mach_minutes t =
  let y = t.year in
  let days =
    add (add (days_before_year y) (days_before_month y t.month))
      (sub t.day (Uint63.of_int (1)))
  in
  add (mul (add (mul days (Uint63.of_int (24))) t.hour) (Uint63.of_int (60)))
    t.minute

(** val key_al : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let key_al ma r i =
  if eqb ma r
  then add (add (mul ma (Uint63.of_int (20000))) (Uint63.of_int (5000)))
         (mul (Uint63.of_int (2)) i)
  else add (add (mul ma (Uint63.of_int (20000))) (Uint63.of_int (15000))) i

(** val key_rh : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let key_rh ma r i =
  if eqb ma r
  then add (add (mul ma (Uint63.of_int (20000))) (Uint63.of_int (5001)))
         (mul (Uint63.of_int (2)) i)
  else add (mul r (Uint63.of_int (20000))) i

(** val fill :
    uint datetime Marray.t -> uint datetime Marray.t -> Uint63.t -> Uint63.t
    -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let rec fill xa xd c n k a r =
  if bdec (ltb k n)
  then let ma = mach_minutes (get xa k) in
       let r0 = add (mach_minutes (get xd k)) c in
       fill xa xd c n (add k (Uint63.of_int (1))) (set a k (key_al ma r0 k))
         (set r k (key_rh ma r0 k))
  else (a, r)

(** val min_rooms_impl :
    uint -> uint datetime Marray.t -> uint datetime Marray.t -> uint **)

let min_rooms_impl c xa xd =
  let n = length xa in
  let (a, r) =
    fill xa xd c n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (make n (Uint63.of_int (0)))
  in
  let a' = sort_all a in
  let r' = sort_all r in
  sweep a' r' n (Uint63.of_int (0)) (Uint63.of_int (0)) (Uint63.of_int (0))

(** val min_rooms :
    uint -> uint datetime Marray.t -> uint datetime Marray.t -> uint **)

let min_rooms =
  min_rooms_impl
