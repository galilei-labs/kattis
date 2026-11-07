
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

(** val sum_loop : uint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec sum_loop a i acc =
  if bdec (ltb (Uint63.of_int (0)) i)
  then sum_loop a (sub i (Uint63.of_int (1)))
         (add acc (get a (sub i (Uint63.of_int (1)))))
  else acc

(** val cell_loop :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
    Marray.t **)

let rec cell_loop t w x c s =
  if bdec (ltb s w)
  then cell_loop
         (if get t (add (mul (sub c (Uint63.of_int (1))) w) (sub s x))
          then set t (add (mul c w) s) true
          else t)
         w x c (add s (Uint63.of_int (1)))
  else t

(** val row_loop :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool Marray.t **)

let rec row_loop t w x c =
  if bdec (ltb (Uint63.of_int (0)) c)
  then row_loop (cell_loop t w x c x) w x (sub c (Uint63.of_int (1)))
  else t

(** val item_loop :
    uint Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    bool Marray.t **)

let rec item_loop a t w k i =
  if bdec (ltb (Uint63.of_int (0)) i)
  then item_loop a (row_loop t w (get a (sub i (Uint63.of_int (1)))) k) w k
         (sub i (Uint63.of_int (1)))
  else t

(** val best_loop :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec best_loop t w h k s =
  if (||) (get t (add (mul h w) s)) (get t (add (mul k w) s))
  then s
  else if bdec (ltb (Uint63.of_int (0)) s)
       then best_loop t w h k (sub s (Uint63.of_int (1)))
       else (Uint63.of_int (0))

(** val tugofwar_impl : uint Marray.t -> uint * uint **)

let tugofwar_impl a =
  let n = length a in
  let s = sum_loop a n (Uint63.of_int (0)) in
  let half = div s (Uint63.of_int (2)) in
  let w = add half (Uint63.of_int (1)) in
  let h = div n (Uint63.of_int (2)) in
  let k = sub n h in
  let t0 =
    set (make (mul (add k (Uint63.of_int (1))) w) false) (Uint63.of_int (0))
      true
  in
  let t = item_loop a t0 w k n in
  let b = best_loop t w h k half in (b, (sub s b))

module TugofwarImpl =
 struct
  (** val tugofwar : uint Marray.t -> uint * uint **)

  let tugofwar =
    tugofwar_impl
 end
