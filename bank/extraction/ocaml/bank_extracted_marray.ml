
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

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

(** val init_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec init_loop m k a =
  if bdec (ltb k m)
  then init_loop m (add k (Uint63.of_int (1))) (set a k k)
  else a

(** val take_left :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let take_left cash src mid hi i j =
  if ltb i mid
  then if ltb j hi
       then leb (get cash (get src j)) (get cash (get src i))
       else true
  else false

(** val merge_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec merge_loop cash src mid hi i j k dst =
  if bdec (ltb k hi)
  then if take_left cash src mid hi i j
       then merge_loop cash src mid hi (add i (Uint63.of_int (1))) j
              (add k (Uint63.of_int (1))) (set dst k (get src i))
       else merge_loop cash src mid hi i (add j (Uint63.of_int (1)))
              (add k (Uint63.of_int (1))) (set dst k (get src j))
  else dst

(** val copy_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec copy_loop src hi k dst =
  if bdec (ltb k hi)
  then copy_loop src hi (add k (Uint63.of_int (1))) (set dst k (get src k))
  else dst

(** val msort :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort cash a b lo len =
  if bdec (ltb (Uint63.of_int (1)) len)
  then let len1 = div len (Uint63.of_int (2)) in
       let mid = add lo len1 in
       let hi = add lo len in
       let (a1, b1) = msort cash a b lo len1 in
       let (a2, b2) = msort cash a1 b1 mid (sub len len1) in
       let b3 = merge_loop cash a2 mid hi lo mid lo b2 in
       let a3 = copy_loop b3 hi lo a2 in (a3, b3)
  else (a, b)

(** val find :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t **)

let rec find a x =
  let p = get a x in
  if bdec (ltb p x)
  then let (a1, r) = find a p in ((set a1 x r), r)
  else (a, x)

(** val greedy_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let rec greedy_loop cash dl perm n l j uf tot =
  if bdec (ltb j n)
  then let i = get perm j in
       let d = get dl i in
       let c = if ltb d l then add d (Uint63.of_int (1)) else l in
       let (uf1, r) = find uf c in
       if eqb r (Uint63.of_int (0))
       then greedy_loop cash dl perm n l (add j (Uint63.of_int (1))) uf1 tot
       else greedy_loop cash dl perm n l (add j (Uint63.of_int (1)))
              (set uf1 r (sub r (Uint63.of_int (1)))) (add tot (get cash i))
  else tot

(** val bank_impl : uint -> uint Marray.t -> uint Marray.t -> uint **)

let bank_impl t cash dl =
  let n = length cash in
  let p0 = init_loop n (Uint63.of_int (0)) (make n (Uint63.of_int (0))) in
  let p =
    fst (msort cash p0 (make n (Uint63.of_int (0))) (Uint63.of_int (0)) n)
  in
  let l = if ltb t n then t else n in
  let uf =
    init_loop (add l (Uint63.of_int (1))) (Uint63.of_int (0))
      (make (add l (Uint63.of_int (1))) (Uint63.of_int (0)))
  in
  greedy_loop cash dl p n l (Uint63.of_int (0)) uf (Uint63.of_int (0))

(** val bank : uint -> uint Marray.t -> uint Marray.t -> uint **)

let bank =
  bank_impl
