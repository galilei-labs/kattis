
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

type buffer = Uint63.t Marray.t * Uint63.t Marray.t

(** val alen : Uint63.t Marray.t -> Uint63.t **)

let alen =
  length

(** val bget : buffer -> Uint63.t -> Uint63.t **)

let bget t i =
  let (a, b) = t in if ltb i (alen a) then get a i else get b (sub i (alen a))

(** val bset : buffer -> Uint63.t -> Uint63.t -> buffer **)

let bset t i v =
  let (a, b) = t in
  if ltb i (alen a) then ((set a i v), b) else (a, (set b (sub i (alen a)) v))

(** val bmake : Uint63.t -> buffer **)

let bmake n =
  ((make n (Uint63.of_int (0))),
    (make
      (if ltb (Uint63.of_int (4194303)) n
       then sub n (Uint63.of_int (4194303))
       else (Uint63.of_int (0)))
      (Uint63.of_int (0))))

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val fall :
    string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec fall xp tbl c q =
  if eqb (get0 xp q) c
  then add q (Uint63.of_int (1))
  else if bdec (ltb (Uint63.of_int (0)) q)
       then let q' = get tbl (sub q (Uint63.of_int (1))) in
            if bdec (ltb q' q) then fall xp tbl c q' else (Uint63.of_int (0))
       else (Uint63.of_int (0))

(** val build :
    string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec build xp m tbl i q =
  if bdec (ltb i m)
  then let r = fall xp tbl (get0 xp i) q in
       build xp m (set tbl i r) (add i (Uint63.of_int (1))) r
  else tbl

(** val copy : buffer -> buffer -> Uint63.t -> Uint63.t -> buffer **)

let rec copy buf res c k =
  if bdec (ltb k c)
  then copy buf (bset res k (bget buf k)) c (add k (Uint63.of_int (1)))
  else res

(** val scan :
    string -> string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> buffer
    -> Uint63.t -> Uint63.t -> Uint63.t -> buffer **)

let rec scan xp xt tbl m n buf i q cnt =
  if bdec (ltb i n)
  then let r = fall xp tbl (get0 xt i) q in
       if eqb r m
       then scan xp xt tbl m n
              (bset buf cnt (sub (add i (Uint63.of_int (1))) m))
              (add i (Uint63.of_int (1)))
              (get tbl (sub m (Uint63.of_int (1))))
              (add cnt (Uint63.of_int (1)))
       else scan xp xt tbl m n buf (add i (Uint63.of_int (1))) r cnt
  else copy buf (bmake cnt) cnt (Uint63.of_int (0))

(** val find_all_impl : string -> string -> buffer **)

let find_all_impl xp xt =
  let m = length0 xp in
  let n = length0 xt in
  if ltb n m
  then bmake (Uint63.of_int (0))
  else let tbl =
         build xp m (make m (Uint63.of_int (0))) (Uint63.of_int (1))
           (Uint63.of_int (0))
       in
       scan xp xt tbl m n (bmake (add (sub n m) (Uint63.of_int (1))))
         (Uint63.of_int (0)) (Uint63.of_int (0)) (Uint63.of_int (0))

(** val find_all : string -> string -> buffer **)

let find_all =
  find_all_impl
