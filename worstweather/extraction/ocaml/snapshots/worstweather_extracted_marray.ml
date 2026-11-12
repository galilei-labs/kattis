
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

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

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

type answer =
| Ans_true
| Ans_maybe
| Ans_false

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val lb_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec lb_loop ys key lo hi =
  if bdec (ltb lo hi)
  then let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
       if ltsb (get ys mid) key
       then lb_loop ys key (add mid (Uint63.of_int (1))) hi
       else lb_loop ys key lo mid
  else lo

(** val lower_bound :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let lower_bound ys n key =
  lb_loop ys key (Uint63.of_int (0)) n

(** val lg_loop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec lg_loop x k =
  if bdec (ltb (Uint63.of_int (1)) x)
  then lg_loop (div x (Uint63.of_int (2))) (add k (Uint63.of_int (1)))
  else k

(** val lg : Uint63.t -> Uint63.t **)

let lg x =
  lg_loop x (Uint63.of_int (0))

(** val imax : Uint63.t -> Uint63.t -> Uint63.t **)

let imax a b =
  if ltb a b then b else a

(** val copy_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec copy_loop rs n i t =
  if bdec (ltb i n)
  then copy_loop rs n (add i (Uint63.of_int (1))) (set t i (get rs i))
  else t

(** val row_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec row_loop base prev half lim i t =
  if bdec (ltb i lim)
  then row_loop base prev half lim (add i (Uint63.of_int (1)))
         (set t (add base i)
           (imax (get t (add prev i)) (get t (add (add prev i) half))))
  else t

(** val rows_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec rows_loop n l k t =
  if bdec (ltb k l)
  then rows_loop n l (add k (Uint63.of_int (1)))
         (row_loop (mul k n) (mul (sub k (Uint63.of_int (1))) n)
           (lsl0 (Uint63.of_int (1)) (sub k (Uint63.of_int (1))))
           (add (sub n (lsl0 (Uint63.of_int (1)) k)) (Uint63.of_int (1)))
           (Uint63.of_int (0)) t)
  else t

(** val build :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let build rs n l =
  rows_loop n l (Uint63.of_int (1))
    (copy_loop rs n (Uint63.of_int (0)) (make (mul l n) (Uint63.of_int (0))))

(** val rmq :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rmq t n l r =
  let k = lg (sub r l) in
  imax (get t (add (mul k n) l))
    (get t (add (mul k n) (sub r (lsl0 (Uint63.of_int (1)) k))))

(** val below :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let below t n lo j v =
  if ltb lo j then ltb (rmq t n lo j) v else true

(** val answer_query :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> answer **)

let answer_query ys rs t n y x =
  let i = lower_bound ys n y in
  let j = lower_bound ys n x in
  let yk = if ltb i n then eqb (get ys i) y else false in
  let xk = if ltb j n then eqb (get ys j) x else false in
  let lo = if yk then add i (Uint63.of_int (1)) else i in
  if yk
  then if xk
       then if leb (get rs j) (get rs i)
            then if below t n lo j (get rs j)
                 then if eqb (sub j i) (sub x y) then Ans_true else Ans_maybe
                 else Ans_false
            else Ans_false
       else if below t n lo j (get rs i) then Ans_maybe else Ans_false
  else if xk
       then if below t n lo j (get rs j) then Ans_maybe else Ans_false
       else Ans_maybe

(** val q_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    answer Marray.t -> answer Marray.t **)

let rec q_loop ys rs t qy qx n m k out =
  if bdec (ltb k m)
  then q_loop ys rs t qy qx n m (add k (Uint63.of_int (1)))
         (set out k (answer_query ys rs t n (get qy k) (get qx k)))
  else out

(** val worstweather_impl :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> answer Marray.t **)

let worstweather_impl ys rs qy qx =
  let n = length ys in
  let m = length qy in
  let l = add (lg n) (Uint63.of_int (1)) in
  let t = build rs n l in
  q_loop ys rs t qy qx n m (Uint63.of_int (0)) (make m Ans_false)

(** val worstweather :
    sint Marray.t -> uint Marray.t -> sint Marray.t -> sint Marray.t ->
    answer Marray.t **)

let worstweather =
  worstweather_impl
