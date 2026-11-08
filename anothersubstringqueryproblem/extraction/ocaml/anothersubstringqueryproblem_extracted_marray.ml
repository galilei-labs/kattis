
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

type comparison =
| Eq
| Lt
| Gt

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

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

type char63 = Uint63.t

type string = Pstring.t

(** val length0 : string -> Uint63.t **)

let length0 = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val midp : Uint63.t -> Uint63.t -> Uint63.t **)

let midp lo hi =
  add lo (div (sub hi lo) (Uint63.of_int (2)))

(** val cmpt :
    string -> string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    comparison **)

let rec cmpt x t n m p k =
  if bdec (ltb k m)
  then if ltb (add p k) n
       then let a = get0 t k in
            let b = get0 x (add p k) in
            if ltb a b
            then Lt
            else if ltb b a
                 then Gt
                 else cmpt x t n m p (add k (Uint63.of_int (1)))
       else Gt
  else Eq

(** val copy :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copy a b hi k =
  if bdec (ltb k hi)
  then copy a (set b k (get a k)) hi (add k (Uint63.of_int (1)))
  else b

(** val merge :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t **)

let rec merge le src dst mid hi i j k =
  if bdec (ltb k hi)
  then if (&&) (ltb i mid) ((||) (leb hi j) (le (get src i) (get src j)))
       then merge le src (set dst k (get src i)) mid hi
              (add i (Uint63.of_int (1))) j (add k (Uint63.of_int (1)))
       else merge le src (set dst k (get src j)) mid hi i
              (add j (Uint63.of_int (1))) (add k (Uint63.of_int (1)))
  else dst

(** val msort :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort le a b lo hi =
  if bdec ((&&) (ltb lo hi) (ltb (Uint63.of_int (1)) (sub hi lo)))
  then let mid = midp lo hi in
       let (a1, b1) = msort le a b lo mid in
       let (a2, b2) = msort le a1 b1 mid hi in
       let b3 = copy a2 b2 hi lo in ((merge le b3 a2 mid hi lo mid lo), b3)
  else (a, b)

(** val iota_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec iota_loop a n i =
  if bdec (ltb i n)
  then iota_loop (set a i i) n (add i (Uint63.of_int (1)))
  else a

(** val rank_loop :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec rank_loop le sa nr n i =
  if bdec (ltb i n)
  then let p = get sa i in
       let q = get sa (sub i (Uint63.of_int (1))) in
       rank_loop le sa
         (set nr p
           (add (get nr q)
             (if le p q then (Uint63.of_int (0)) else (Uint63.of_int (1)))))
         n (add i (Uint63.of_int (1)))
  else nr

(** val r2 :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let r2 rk h n p =
  if ltb (add p h) n
  then add (get rk (add p h)) (Uint63.of_int (1))
  else (Uint63.of_int (0))

(** val keyle :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let keyle rk h n p q =
  (||) (ltb (get rk p) (get rk q))
    ((&&) (eqb (get rk p) (get rk q)) (leb (r2 rk h n p) (r2 rk h n q)))

(** val sort_round :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let sort_round rk h n =
  fst
    (msort (keyle rk h n)
      (iota_loop (make n (Uint63.of_int (0))) n (Uint63.of_int (0)))
      (make n (Uint63.of_int (0))) (Uint63.of_int (0)) n)

(** val rounds :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let rec rounds n rk h =
  let sa = sort_round rk h n in
  let nr =
    rank_loop (keyle rk h n) sa (make n (Uint63.of_int (0))) n
      (Uint63.of_int (1))
  in
  if bdec
       ((&&) ((&&) (ltb (Uint63.of_int (0)) h) (ltb h n))
         ((&&) (ltb h (sub n h))
           (negb
             (eqb (get nr (get sa (sub n (Uint63.of_int (1)))))
               (sub n (Uint63.of_int (1)))))))
  then rounds n nr (add h h)
  else sa

(** val init_rk :
    string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec init_rk x rk n i =
  if bdec (ltb i n)
  then init_rk x (set rk i (get0 x i)) n (add i (Uint63.of_int (1)))
  else rk

(** val build_sa : string -> Uint63.t -> Uint63.t Marray.t **)

let build_sa x n =
  rounds n (init_rk x (make n (Uint63.of_int (0))) n (Uint63.of_int (0)))
    (Uint63.of_int (1))

(** val bs : (Uint63.t -> bool) -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec bs p lo hi =
  if bdec (ltb lo hi)
  then if p (midp lo hi)
       then bs p lo (midp lo hi)
       else bs p (add (midp lo hi) (Uint63.of_int (1))) hi
  else lo

(** val ins :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t Marray.t **)

let rec ins l r c nx x d v =
  if bdec (ltb (Uint63.of_int (0)) d)
  then let half = lsl0 (Uint63.of_int (1)) (sub d (Uint63.of_int (1))) in
       let y = add nx d in
       if ltb v half
       then let (p, cq) = ins l r c nx (get l x) (sub d (Uint63.of_int (1))) v
            in
            let (lq, rq) = p in
            (((set lq y (add nx (sub d (Uint63.of_int (1))))),
            (set rq y (get rq x))),
            (set cq y (add (get cq x) (Uint63.of_int (1)))))
       else let (p, cq) =
              ins l r c nx (get r x) (sub d (Uint63.of_int (1))) (sub v half)
            in
            let (lq, rq) = p in
            (((set lq y (get lq x)),
            (set rq y (add nx (sub d (Uint63.of_int (1)))))),
            (set cq y (add (get cq x) (Uint63.of_int (1)))))
  else ((l, r), (set c nx (add (get c x) (Uint63.of_int (1)))))

(** val qry :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec qry l r c a b d k =
  if bdec (ltb (Uint63.of_int (0)) d)
  then let cl = sub (get c (get l b)) (get c (get l a)) in
       if leb k cl
       then qry l r c (get l a) (get l b) (sub d (Uint63.of_int (1))) k
       else add (lsl0 (Uint63.of_int (1)) (sub d (Uint63.of_int (1))))
              (qry l r c (get r a) (get r b) (sub d (Uint63.of_int (1)))
                (sub k cl))
  else (Uint63.of_int (0))

(** val depth_loop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec depth_loop n d =
  if bdec (ltb d (Uint63.of_int (20)))
  then if ltb (lsl0 (Uint63.of_int (1)) d) n
       then depth_loop n (add d (Uint63.of_int (1)))
       else d
  else d

(** val build :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t Marray.t **)

let rec build sa l r c roots n d i nx =
  if bdec (ltb i n)
  then let (p, cq) = ins l r c nx (get roots i) d (get sa i) in
       let (lq, rq) = p in
       build sa lq rq cq (set roots (add i (Uint63.of_int (1))) (add nx d)) n
         d (add i (Uint63.of_int (1))) (add (add nx d) (Uint63.of_int (1)))
  else (((l, r), c), roots)

(** val cmp_at :
    string -> string -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    -> comparison **)

let cmp_at x t n m sa i =
  cmpt x t n m (get sa i) (Uint63.of_int (0))

(** val answer1 :
    string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> string
    -> Uint63.t -> Uint63.t **)

let answer1 x n sa l r c roots d t k =
  let m = length0 t in
  let lo =
    bs (fun i -> match cmp_at x t n m sa i with
                 | Gt -> false
                 | _ -> true)
      (Uint63.of_int (0)) n
  in
  let hi =
    bs (fun i -> match cmp_at x t n m sa i with
                 | Lt -> true
                 | _ -> false)
      (Uint63.of_int (0)) n
  in
  if leb k (sub hi lo)
  then add (qry l r c (get roots lo) (get roots hi) d k) (Uint63.of_int (1))
  else sub (Uint63.of_int (0)) (Uint63.of_int (1))

(** val qloop :
    string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> string
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec qloop x n sa l r c roots d ts ks out q q0 =
  if bdec (ltb q q0)
  then qloop x n sa l r c roots d ts ks
         (set out q (answer1 x n sa l r c roots d (get ts q) (get ks q)))
         (add q (Uint63.of_int (1))) q0
  else out

(** val kth_occurrences_impl :
    string -> string Marray.t -> uint Marray.t -> sint Marray.t **)

let kth_occurrences_impl x ts ks =
  let n = length0 x in
  let sa = build_sa x n in
  let d = depth_loop n (Uint63.of_int (0)) in
  let m = add (mul n (add d (Uint63.of_int (1)))) (Uint63.of_int (1)) in
  let (p, roots) =
    build sa (make m (Uint63.of_int (0))) (make m (Uint63.of_int (0)))
      (make m (Uint63.of_int (0)))
      (make (add n (Uint63.of_int (1))) (Uint63.of_int (0))) n d
      (Uint63.of_int (0)) (Uint63.of_int (1))
  in
  let (p0, c) = p in
  let (l, r) = p0 in
  let q = length ts in
  qloop x n sa l r c roots d ts ks (make q (Uint63.of_int (0)))
    (Uint63.of_int (0)) q

(** val kth_occurrences :
    string -> string Marray.t -> uint Marray.t -> sint Marray.t **)

let kth_occurrences =
  kth_occurrences_impl
