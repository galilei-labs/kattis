
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val area_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec area_loop x y m i acc =
  if bdec (ltb i m)
  then area_loop x y m (add i (Uint63.of_int (1)))
         (sub (add acc (mul (get x i) (get y (add i (Uint63.of_int (1))))))
           (mul (get x (add i (Uint63.of_int (1)))) (get y i)))
  else acc

(** val signed_area2_impl : sint Marray.t -> sint Marray.t -> sint **)

let signed_area2_impl x y =
  let m = sub (length x) (Uint63.of_int (1)) in
  let s = area_loop x y m (Uint63.of_int (0)) (Uint63.of_int (0)) in
  sub (add s (mul (get x m) (get y (Uint63.of_int (0)))))
    (mul (get x (Uint63.of_int (0))) (get y m))

module PolygonareaImpl =
 struct
  (** val signed_area2 : sint Marray.t -> sint Marray.t -> sint **)

  let signed_area2 =
    signed_area2_impl
 end
