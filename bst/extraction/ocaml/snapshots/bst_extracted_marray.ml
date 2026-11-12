
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

type color =
| Red
| Black

type rbt =
| RE
| RN of color * rbt * Uint63.t * rbt

(** val lbal : rbt -> Uint63.t -> rbt -> rbt **)

let lbal l k r =
  match l with
  | RE -> RN (Black, l, k, r)
  | RN (c0, a, x, c) ->
    (match c0 with
     | Red ->
       (match a with
        | RE ->
          (match c with
           | RE -> RN (Black, l, k, r)
           | RN (c1, b, y, c2) ->
             (match c1 with
              | Red ->
                RN (Red, (RN (Black, a, x, b)), y, (RN (Black, c2, k, r)))
              | Black -> RN (Black, l, k, r)))
        | RN (c1, a0, x0, b) ->
          (match c1 with
           | Red ->
             RN (Red, (RN (Black, a0, x0, b)), x, (RN (Black, c, k, r)))
           | Black ->
             (match c with
              | RE -> RN (Black, l, k, r)
              | RN (c2, b0, y, c3) ->
                (match c2 with
                 | Red ->
                   RN (Red, (RN (Black, a, x, b0)), y, (RN (Black, c3, k, r)))
                 | Black -> RN (Black, l, k, r)))))
     | Black -> RN (Black, l, k, r))

(** val rbal : rbt -> Uint63.t -> rbt -> rbt **)

let rbal l k r = match r with
| RE -> RN (Black, l, k, r)
| RN (c0, b, y, d) ->
  (match c0 with
   | Red ->
     (match b with
      | RE ->
        (match d with
         | RE -> RN (Black, l, k, r)
         | RN (c1, c, z, d0) ->
           (match c1 with
            | Red ->
              RN (Red, (RN (Black, l, k, b)), y, (RN (Black, c, z, d0)))
            | Black -> RN (Black, l, k, r)))
      | RN (c1, b0, y0, c) ->
        (match c1 with
         | Red -> RN (Red, (RN (Black, l, k, b0)), y0, (RN (Black, c, y, d)))
         | Black ->
           (match d with
            | RE -> RN (Black, l, k, r)
            | RN (c2, c3, z, d0) ->
              (match c2 with
               | Red ->
                 RN (Red, (RN (Black, l, k, b)), y, (RN (Black, c3, z, d0)))
               | Black -> RN (Black, l, k, r)))))
   | Black -> RN (Black, l, k, r))

(** val rb_ins : Uint63.t -> rbt -> rbt **)

let rec rb_ins y t = match t with
| RE -> RN (Red, RE, y, RE)
| RN (c, l, k, r) ->
  if ltb y k
  then (match c with
        | Red -> RN (Red, (rb_ins y l), k, r)
        | Black -> lbal (rb_ins y l) k r)
  else if ltb k y
       then (match c with
             | Red -> RN (Red, l, k, (rb_ins y r))
             | Black -> rbal l k (rb_ins y r))
       else t

(** val make_black : rbt -> rbt **)

let make_black = function
| RE -> RE
| RN (_, l, k, r) -> RN (Black, l, k, r)

(** val rb_insert : Uint63.t -> rbt -> rbt **)

let rb_insert y t =
  make_black (rb_ins y t)

(** val around :
    Uint63.t -> rbt -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let rec around y t p s =
  match t with
  | RE -> (p, s)
  | RN (_, l, k, r) -> if ltb y k then around y l p k else around y r k s

(** val imax : Uint63.t -> Uint63.t -> Uint63.t **)

let imax u v =
  if ltb u v then v else u

(** val loop :
    uint Marray.t -> Uint63.t -> Uint63.t -> rbt -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec loop x n j t d c o =
  if bdec (ltb j n)
  then let y = get x j in
       let ps = around y t (Uint63.of_int (0)) (add n (Uint63.of_int (1))) in
       let e =
         add (Uint63.of_int (1)) (imax (get d (fst ps)) (get d (snd ps)))
       in
       let c' = sub (add c e) (Uint63.of_int (1)) in
       loop x n (add j (Uint63.of_int (1))) (rb_insert y t) (set d y e) c'
         (set o j c')
  else o

(** val bst_impl : uint Marray.t -> uint Marray.t **)

let bst_impl x =
  let n = length x in
  loop x n (Uint63.of_int (0)) RE
    (make (add n (Uint63.of_int (2))) (Uint63.of_int (0)))
    (Uint63.of_int (0)) (make n (Uint63.of_int (0)))

(** val bst : uint Marray.t -> uint Marray.t **)

let bst =
  bst_impl
