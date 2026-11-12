
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

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val item_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> bool
    array -> Uint63.t array * bool array **)

let rec item_loop v w base k row dec =
  if bdec (ltb w k)
  then let c = sub k (Uint63.of_int (1)) in
       let cand =
         add ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row (sub c w)) v
       in
       if ltb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row c) cand
       then item_loop v w base c
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) row c
                cand)
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) dec
                (add base c) true)
       else item_loop v w base c row dec
  else (row, dec)

(** val items_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t array -> bool array -> Uint63.t array * bool array **)

let rec items_loop xv xw n c1 i row dec =
  if bdec (ltb i n)
  then let rd =
         item_loop ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xv i)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xw i) (mul i c1)
           c1 row dec
       in
       items_loop xv xw n c1 (add i (Uint63.of_int (1))) (fst rd) (snd rd)
  else (row, dec)

(** val walk :
    Uint63.t array -> bool array -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t array -> Uint63.t * Uint63.t array **)

let rec walk xw dec c1 i c k out =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let j = sub i (Uint63.of_int (1)) in
       if (fun a i -> Array.unsafe_get a (Uint63.hash i)) dec
            (add (mul j c1) c)
       then walk xw dec c1 j
              (sub c ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xw j))
              (add k (Uint63.of_int (1)))
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) out k j)
       else walk xw dec c1 j c k out
  else (k, out)

(** val copy_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array **)

let rec copy_loop src dst m j =
  if bdec (ltb j m)
  then copy_loop src
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) dst j
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) src j))
         m (add j (Uint63.of_int (1)))
  else dst

(** val knapsack_impl :
    Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t * Uint63.t array **)

let knapsack_impl cw xv xw =
  let n = (fun a -> Uint63.of_int (Array.length a)) xv in
  let c1 = add cw (Uint63.of_int (1)) in
  let rd =
    items_loop xv xw n c1 (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) c1 (Uint63.of_int (0)))
      ((fun n d -> Array.make (Uint63.hash n) d) (mul n c1) false)
  in
  let bestv = (fun a i -> Array.unsafe_get a (Uint63.hash i)) (fst rd) cw in
  let ko =
    walk xw (snd rd) c1 n cw (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))
  in
  let k = fst ko in
  (bestv,
  (copy_loop (snd ko)
    ((fun n d -> Array.make (Uint63.hash n) d) k (Uint63.of_int (0))) k
    (Uint63.of_int (0))))

(** val knapsack : uint -> uint array -> uint array -> uint * uint array **)

let knapsack =
  knapsack_impl
