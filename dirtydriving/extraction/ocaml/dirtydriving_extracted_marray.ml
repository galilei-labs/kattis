
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

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

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val split_ok : Uint63.t -> Uint63.t -> bool **)

let split_ok lo hi =
  (&&) (ltb lo hi) (ltb (Uint63.of_int (1)) (sub hi lo))

(** val midp : Uint63.t -> Uint63.t -> Uint63.t **)

let midp lo hi =
  add lo (div (sub hi lo) (Uint63.of_int (2)))

(** val take_left :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let take_left a mid hi i j =
  if ltb i mid
  then if ltb j hi then leb (get a i) (get a j) else true
  else false

(** val merge_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec merge_loop a t mid hi i j k =
  if bdec (ltb k hi)
  then if take_left a mid hi i j
       then merge_loop a (set t k (get a i)) mid hi
              (add i (Uint63.of_int (1))) j (add k (Uint63.of_int (1)))
       else merge_loop a (set t k (get a j)) mid hi i
              (add j (Uint63.of_int (1))) (add k (Uint63.of_int (1)))
  else t

(** val copy_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copy_loop src dst hi k =
  if bdec (ltb k hi)
  then copy_loop src (set dst k (get src k)) hi (add k (Uint63.of_int (1)))
  else dst

(** val msort :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort a t lo hi =
  if bdec (split_ok lo hi)
  then let (a1, t1) = msort a t lo (midp lo hi) in
       let (a2, t2) = msort a1 t1 (midp lo hi) hi in
       let t3 = merge_loop a2 t2 (midp lo hi) hi lo (midp lo hi) lo in
       ((copy_loop t3 a2 hi lo), t3)
  else (a, t)

(** val need : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let need p s0 x k =
  let t = add (mul p (add k (Uint63.of_int (1)))) s0 in
  if ltb x t then sub t x else (Uint63.of_int (0))

(** val max_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec max_loop s p s0 n k acc =
  if bdec (ltb k n)
  then let v = need p s0 (get s k) k in
       max_loop s p s0 n (add k (Uint63.of_int (1)))
         (if ltb acc v then v else acc)
  else acc

(** val dirtydriving_impl : uint -> uint Marray.t -> uint **)

let dirtydriving_impl p d =
  let n = length d in
  let s = fst (msort d (make n (Uint63.of_int (0))) (Uint63.of_int (0)) n) in
  max_loop s p (get s (Uint63.of_int (0))) n (Uint63.of_int (0))
    (Uint63.of_int (0))

(** val dirtydriving : uint -> uint Marray.t -> uint **)

let dirtydriving =
  dirtydriving_impl
