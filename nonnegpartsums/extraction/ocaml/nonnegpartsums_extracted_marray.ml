
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

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

(** val prefix_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec prefix_loop x n i p =
  if bdec (ltb i n)
  then prefix_loop x n (add i (Uint63.of_int (1)))
         (set p (add i (Uint63.of_int (1))) (add (get p i) (get x i)))
  else p

(** val qv :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let qv p n tot j =
  if leb j n then get p j else add tot (get p (sub j n))

(** val pop_front :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec pop_front dq n j h t =
  if bdec (ltb h t)
  then if leb (add (get dq (mod0 h n)) n) j
       then pop_front dq n j (add h (Uint63.of_int (1))) t
       else h
  else h

(** val pop_back :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec pop_back dq p n tot qj h t =
  if bdec (ltb h t)
  then if lesb qj (qv p n tot (get dq (mod0 (sub t (Uint63.of_int (1))) n)))
       then pop_back dq p n tot qj h (sub t (Uint63.of_int (1)))
       else t
  else t

(** val sweep :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t **)

let rec sweep p n tot m j h t cnt dq =
  if bdec (ltb j m)
  then let h1 = pop_front dq n j h t in
       let qj = qv p n tot j in
       let t1 = pop_back dq p n tot qj h1 t in
       let dq1 = set dq (mod0 t1 n) j in
       let cnt1 =
         if leb n j
         then if lesb (qv p n tot (sub j n))
                   (qv p n tot (get dq1 (mod0 h1 n)))
              then add cnt (Uint63.of_int (1))
              else cnt
         else cnt
       in
       sweep p n tot m (add j (Uint63.of_int (1))) h1
         (add t1 (Uint63.of_int (1))) cnt1 dq1
  else cnt

(** val count_impl : sint Marray.t -> uint **)

let count_impl x =
  let n = length x in
  let p =
    prefix_loop x n (Uint63.of_int (0))
      (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))
  in
  let tot = get p n in
  sweep p n tot (add n n) (Uint63.of_int (1)) (Uint63.of_int (0))
    (Uint63.of_int (0)) (Uint63.of_int (0)) (make n (Uint63.of_int (0)))

(** val count_good_shifts : sint Marray.t -> uint **)

let count_good_shifts =
  count_impl
