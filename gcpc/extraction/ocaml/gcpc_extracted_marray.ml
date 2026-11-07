
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

type tree =
| Leaf
| Node of tree * Uint63.t * tree * Uint63.t * Uint63.t

(** val height : tree -> Uint63.t **)

let height = function
| Leaf -> (Uint63.of_int (0))
| Node (_, _, _, _, h) -> h

(** val size : tree -> Uint63.t **)

let size = function
| Leaf -> (Uint63.of_int (0))
| Node (_, _, _, s, _) -> s

(** val mk : tree -> Uint63.t -> tree -> tree **)

let mk l k r =
  Node (l, k, r, (add (add (size l) (size r)) (Uint63.of_int (1))),
    (if ltb (height l) (height r)
     then add (height r) (Uint63.of_int (1))
     else add (height l) (Uint63.of_int (1))))

(** val bal : tree -> Uint63.t -> tree -> tree **)

let bal l k r =
  let hl = height l in
  let hr = height r in
  if ltb (add hr (Uint63.of_int (2))) hl
  then (match l with
        | Leaf -> mk l k r
        | Node (ll, lk, lr, _, _) ->
          if leb (height lr) (height ll)
          then mk ll lk (mk lr k r)
          else (match lr with
                | Leaf -> mk l k r
                | Node (lrl, lrk, lrr, _, _) ->
                  mk (mk ll lk lrl) lrk (mk lrr k r)))
  else if ltb (add hl (Uint63.of_int (2))) hr
       then (match r with
             | Leaf -> mk l k r
             | Node (rl, rk, rr, _, _) ->
               if leb (height rl) (height rr)
               then mk (mk l k rl) rk rr
               else (match rl with
                     | Leaf -> mk l k r
                     | Node (rll, rlk, rlr, _, _) ->
                       mk (mk l k rll) rlk (mk rlr rk rr)))
       else mk l k r

(** val insert : Uint63.t -> tree -> tree **)

let rec insert x t = match t with
| Leaf -> mk Leaf x Leaf
| Node (l, k, r, _, _) ->
  if ltb x k
  then bal (insert x l) k r
  else if ltb k x then bal l k (insert x r) else t

(** val remove_min : tree -> Uint63.t -> tree -> Uint63.t * tree **)

let rec remove_min l k r =
  match l with
  | Leaf -> (k, r)
  | Node (ll, lk, lr, _, _) ->
    let (m, l') = remove_min ll lk lr in (m, (bal l' k r))

(** val merge : tree -> tree -> tree **)

let merge l r =
  match l with
  | Leaf -> r
  | Node (_, _, _, _, _) ->
    (match r with
     | Leaf -> l
     | Node (rl, rk, rr, _, _) ->
       let (m, r') = remove_min rl rk rr in bal l m r')

(** val delete : Uint63.t -> tree -> tree **)

let rec delete x = function
| Leaf -> Leaf
| Node (l, k, r, _, _) ->
  if ltb x k
  then bal (delete x l) k r
  else if ltb k x then bal l k (delete x r) else merge l r

(** val count_lt : Uint63.t -> tree -> Uint63.t **)

let rec count_lt q = function
| Leaf -> (Uint63.of_int (0))
| Node (l, k, r, _, _) ->
  if ltb k q
  then add (add (size l) (Uint63.of_int (1))) (count_lt q r)
  else count_lt q l

(** val kD : Uint63.t **)

let kD =
  (Uint63.of_int (17592186044416))

(** val kE : Uint63.t **)

let kE =
  (Uint63.of_int (131072))

(** val k0 : Uint63.t **)

let k0 =
  (Uint63.of_int (2305825417027649536))

(** val init_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> tree -> Uint63.t
    Marray.t * tree **)

let rec init_loop n1 k keys t =
  if bdec (ltb k n1)
  then let key = add k0 k in
       init_loop n1 (add k (Uint63.of_int (1))) (set keys k key)
         (insert key t)
  else (keys, t)

(** val ev_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> tree -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec ev_loop xt xp m j keys t out =
  if bdec (ltb j m)
  then let a = get xt j in
       let old = get keys a in
       let new0 = add (sub old kD) (mul (get xp j) kE) in
       let keys' = set keys a new0 in
       let t' = insert new0 (delete old t) in
       let ans =
         add
           (count_lt
             (sub (get keys' (Uint63.of_int (1))) (Uint63.of_int (1))) t')
           (Uint63.of_int (1))
       in
       ev_loop xt xp m (add j (Uint63.of_int (1))) keys' t' (set out j ans)
  else out

(** val gcpc_impl :
    uint -> uint Marray.t -> uint Marray.t -> uint Marray.t **)

let gcpc_impl n xt xp =
  let m = length xt in
  let n1 = add n (Uint63.of_int (1)) in
  let (keys, t) =
    init_loop n1 (Uint63.of_int (1)) (make n1 (Uint63.of_int (0))) Leaf
  in
  ev_loop xt xp m (Uint63.of_int (0)) keys t (make m (Uint63.of_int (0)))

module GcpcImpl =
 struct
  (** val gcpc : uint -> uint Marray.t -> uint Marray.t -> uint Marray.t **)

  let gcpc =
    gcpc_impl
 end
