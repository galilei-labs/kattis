
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

(** val pick : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let pick h s l =
  if ltb (add l (Uint63.of_int (1))) s
  then if ltb (get h l) (get h (add l (Uint63.of_int (1))))
       then add l (Uint63.of_int (1))
       else l
  else l

(** val sift_up : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let rec sift_up h i =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let q = div (sub i (Uint63.of_int (1))) (Uint63.of_int (2)) in
       let vi = get h i in
       let vq = get h q in
       if bdec (ltb vq vi) then sift_up (set (set h i vq) q vi) q else h
  else h

(** val sift_down :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec sift_down h s i =
  if bdec (ltb i (div s (Uint63.of_int (2))))
  then let c = pick h s (add (mul (Uint63.of_int (2)) i) (Uint63.of_int (1)))
       in
       let vi = get h i in
       let vc = get h c in
       if bdec (ltb vi vc) then sift_down (set (set h i vc) c vi) s c else h
  else h

(** val insert :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let insert h s v =
  sift_up (set h s v) s

(** val extract : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let extract h s =
  let s1 = sub s (Uint63.of_int (1)) in
  sift_down (set h (Uint63.of_int (0)) (get h s1)) s1 (Uint63.of_int (0))

(** val step :
    ((Uint63.t Marray.t * Uint63.t) * Uint63.t Marray.t) -> Uint63.t ->
    Uint63.t -> (Uint63.t Marray.t * Uint63.t) * Uint63.t Marray.t **)

let step st yr sv =
  let (p, t) = st in
  let (h, s) = p in
  if eqb yr (Uint63.of_int (2011))
  then (((insert h s sv), (add s (Uint63.of_int (1)))), t)
  else ((h, s), (set t (sub yr (Uint63.of_int (2011))) sv))

(** val fill :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    ((Uint63.t Marray.t * Uint63.t) * Uint63.t Marray.t) -> (Uint63.t
    Marray.t * Uint63.t) * Uint63.t Marray.t **)

let rec fill ys ps m i st =
  if bdec (ltb i m)
  then fill ys ps m (add i (Uint63.of_int (1)))
         (step st (get ys i) (get ps i))
  else st

(** val sim :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t option **)

let rec sim t h n p s d =
  if bdec (ltb d n)
  then if eqb s (Uint63.of_int (0))
       then None
       else let top = get h (Uint63.of_int (0)) in
            if eqb top p
            then Some (add (Uint63.of_int (2011)) d)
            else if ltb (add d (Uint63.of_int (1))) n
                 then sim t
                        (insert (extract h s) (sub s (Uint63.of_int (1)))
                          (get t (add d (Uint63.of_int (1)))))
                        n p s (add d (Uint63.of_int (1)))
                 else None
  else None

(** val knigs_impl :
    uint -> uint -> uint -> uint -> uint Marray.t -> uint Marray.t -> uint
    option **)

let knigs_impl _ n y p ys ps =
  let m = length ys in
  let st0 =
    step (((make (add m (Uint63.of_int (1))) (Uint63.of_int (0))),
      (Uint63.of_int (0))), (make n (Uint63.of_int (0)))) y p
  in
  let (p0, t) = fill ys ps m (Uint63.of_int (0)) st0 in
  let (h, s) = p0 in sim t h n p s (Uint63.of_int (0))

module KnigsoftheforestImpl =
 struct
  (** val knigsoftheforest :
      uint -> uint -> uint -> uint -> uint Marray.t -> uint Marray.t -> uint
      option **)

  let knigsoftheforest =
    knigs_impl
 end
