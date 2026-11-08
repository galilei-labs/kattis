
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

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

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val merge :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t **)

let rec merge src dst mid hi i j k c =
  if bdec (ltb i mid)
  then if bdec (ltb j hi)
       then let x = get src i in
            let y = get src j in
            if ltb y x
            then merge src (set dst k y) mid hi i (add j (Uint63.of_int (1)))
                   (add k (Uint63.of_int (1))) (add c (sub mid i))
            else merge src (set dst k x) mid hi (add i (Uint63.of_int (1))) j
                   (add k (Uint63.of_int (1))) c
       else merge src (set dst k (get src i)) mid hi
              (add i (Uint63.of_int (1))) j (add k (Uint63.of_int (1))) c
  else if bdec (ltb j hi)
       then merge src (set dst k (get src j)) mid hi i
              (add j (Uint63.of_int (1))) (add k (Uint63.of_int (1))) c
       else (dst, c)

(** val msort :
    bool -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec msort b lo hi w s c =
  if bdec (ltb (Uint63.of_int (1)) (sub hi lo))
  then let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
       let (p, c1) = msort (negb b) lo mid w s c in
       let (w1, s1) = p in
       let (p0, c2) = msort (negb b) mid hi w1 s1 c1 in
       let (w2, s2) = p0 in
       if b
       then let (w3, c3) = merge s2 w2 mid hi lo mid lo c2 in ((w3, s2), c3)
       else let (s3, c3) = merge w2 s2 mid hi lo mid lo c2 in ((w2, s3), c3)
  else if b then ((w, s), c) else ((w, (set s lo (get w lo))), c)

(** val inversions_impl : uint Marray.t -> uint **)

let inversions_impl a =
  let n = length a in
  snd
    (msort true (Uint63.of_int (0)) n (copy a) (make n (Uint63.of_int (0)))
      (Uint63.of_int (0)))

(** val inversions : uint Marray.t -> uint **)

let inversions =
  inversions_impl
