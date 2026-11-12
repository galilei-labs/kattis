
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

(** val length : string -> Uint63.t **)

let length = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

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

(** val copy :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copy buf res c k =
  if bdec (ltb k c)
  then copy buf (set res k (get buf k)) c (add k (Uint63.of_int (1)))
  else res

(** val scan :
    string -> string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec scan xp xt tbl m n buf i q cnt =
  if bdec (ltb i n)
  then let r = fall xp tbl (get0 xt i) q in
       if eqb r m
       then scan xp xt tbl m n
              (set buf cnt (sub (add i (Uint63.of_int (1))) m))
              (add i (Uint63.of_int (1)))
              (get tbl (sub m (Uint63.of_int (1))))
              (add cnt (Uint63.of_int (1)))
       else scan xp xt tbl m n buf (add i (Uint63.of_int (1))) r cnt
  else copy buf (make cnt (Uint63.of_int (0))) cnt (Uint63.of_int (0))

(** val find_all_impl : string -> string -> uint Marray.t **)

let find_all_impl xp xt =
  let m = length xp in
  let n = length xt in
  if ltb n m
  then make (Uint63.of_int (0)) (Uint63.of_int (0))
  else let tbl =
         build xp m (make m (Uint63.of_int (0))) (Uint63.of_int (1))
           (Uint63.of_int (0))
       in
       scan xp xt tbl m n
         (make (add (sub n m) (Uint63.of_int (1))) (Uint63.of_int (0)))
         (Uint63.of_int (0)) (Uint63.of_int (0)) (Uint63.of_int (0))

(** val find_all : string -> string -> uint Marray.t **)

let find_all =
  find_all_impl
