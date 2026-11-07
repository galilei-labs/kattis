
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val horner_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec horner_loop y len x j h =
  if bdec (ltb j len)
  then horner_loop y len x (add j (Uint63.of_int (1)))
         (add (mul h x) (get y j))
  else h

(** val eval_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec eval_loop y len x d =
  if bdec (ltb x len)
  then eval_loop y len (add x (Uint63.of_int (1)))
         (set d x
           (horner_loop y len x (Uint63.of_int (0)) (Uint63.of_int (0))))
  else d

(** val diff_inner :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec diff_inner lo i d =
  if bdec (ltb lo i)
  then let v = sub (get d i) (get d (sub i (Uint63.of_int (1)))) in
       diff_inner lo (sub i (Uint63.of_int (1))) (set d i v)
  else d

(** val diff_outer :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec diff_outer len s d =
  if bdec (ltb s len)
  then diff_outer len (add s (Uint63.of_int (1)))
         (diff_inner s (sub len (Uint63.of_int (1))) d)
  else d

(** val plot_impl : uint -> sint Marray.t -> sint Marray.t **)

let plot_impl _ y =
  let len = length y in
  let d = eval_loop y len (Uint63.of_int (0)) (make len (Uint63.of_int (0)))
  in
  diff_outer len (Uint63.of_int (0)) d

module PlotImpl =
 struct
  (** val plot : uint -> sint Marray.t -> sint Marray.t **)

  let plot =
    plot_impl
 end
