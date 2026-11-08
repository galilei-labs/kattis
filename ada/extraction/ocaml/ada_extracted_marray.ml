
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

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

type uint = Uint63.t

type sint = Uint63.t

(** val acopy : Uint63.t Marray.t -> Uint63.t Marray.t **)

let acopy =
  copy

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val row_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> bool -> Uint63.t
    Marray.t * bool **)

let rec row_loop m j t nz =
  if bdec (ltb j m)
  then let x = sub (get t (add j (Uint63.of_int (1)))) (get t j) in
       row_loop m (add j (Uint63.of_int (1))) (set t j x)
         ((||) nz (negb (eqb x (Uint63.of_int (0)))))
  else (t, nz)

(** val rows_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t **)

let rec rows_loop n k t d =
  if bdec (ltb k n)
  then let r = row_loop (sub n k) (Uint63.of_int (0)) t false in
       rows_loop n (add k (Uint63.of_int (1))) (fst r)
         (if snd r then k else d)
  else (t, d)

(** val sum_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec sum_loop t top e k acc =
  if bdec (ltb k e)
  then sum_loop t top e (add k (Uint63.of_int (1)))
         (add acc (get t (sub top k)))
  else acc

(** val ada_impl : sint Marray.t -> uint * sint **)

let ada_impl a =
  let n = length a in
  let (t, d) = rows_loop n (Uint63.of_int (1)) (acopy a) (Uint63.of_int (0))
  in
  (d,
  (sum_loop t (sub n (Uint63.of_int (1))) (add d (Uint63.of_int (1)))
    (Uint63.of_int (0)) (Uint63.of_int (0))))

(** val ada : sint Marray.t -> uint * sint **)

let ada =
  ada_impl
