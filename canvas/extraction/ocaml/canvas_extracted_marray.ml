
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

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val sift :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec sift h sz i =
  let x = get h i in
  let l = add (mul (Uint63.of_int (2)) i) (Uint63.of_int (1)) in
  if ltb l sz
  then let yl = get h l in
       let r = add l (Uint63.of_int (1)) in
       if (&&) (ltb r sz) (ltb (get h r) yl)
       then let yr = get h r in
            if bdec ((&&) (ltb yr x) (ltb i r))
            then sift (set (set h i yr) r x) sz r
            else h
       else if bdec ((&&) (ltb yl x) (ltb i l))
            then sift (set (set h i yl) l x) sz l
            else h
  else h

(** val build :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec build h sz k =
  if bdec (ltb (Uint63.of_int (0)) k)
  then build (sift h sz (sub k (Uint63.of_int (1)))) sz
         (sub k (Uint63.of_int (1)))
  else h

(** val huff : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec huff h sz acc =
  if bdec (ltb (Uint63.of_int (1)) sz)
  then let a = get h (Uint63.of_int (0)) in
       let sz1 = sub sz (Uint63.of_int (1)) in
       let h1 =
         sift (set h (Uint63.of_int (0)) (get h sz1)) sz1 (Uint63.of_int (0))
       in
       let b = get h1 (Uint63.of_int (0)) in
       let h2 =
         sift (set h1 (Uint63.of_int (0)) (add a b)) sz1 (Uint63.of_int (0))
       in
       huff h2 sz1 (add acc (add a b))
  else acc

(** val canvas_impl : uint Marray.t -> uint **)

let canvas_impl x =
  let sz = length x in
  let h = build (copy x) sz (div sz (Uint63.of_int (2))) in
  huff h sz (Uint63.of_int (0))

module CanvasImpl =
 struct
  (** val canvas : uint Marray.t -> uint **)

  let canvas =
    canvas_impl
 end
