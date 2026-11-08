
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

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

type 'd answer =
| Dist of 'd
| Impossible
| MinusInfinity

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (4611686018427387903))

(** val relax :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t Marray.t -> bool -> Uint63.t Marray.t * bool **)

let relax us vs ws j d ch =
  let du = get d (get us j) in
  if eqb du iNF
  then (d, ch)
  else let v = get vs j in
       let nd = add du (get ws j) in
       if ltsb nd (get d v) then ((set d v nd), true) else (d, ch)

(** val edges_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t Marray.t -> bool -> Uint63.t Marray.t * bool **)

let rec edges_loop us vs ws m j d ch =
  if bdec (ltb j m)
  then let (d', ch') = relax us vs ws j d ch in
       edges_loop us vs ws m (add j (Uint63.of_int (1))) d' ch'
  else (d, ch)

(** val rounds_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec rounds_loop us vs ws m r k d =
  if bdec (ltb k r)
  then let (d', ch) = edges_loop us vs ws m (Uint63.of_int (0)) d false in
       if ch
       then rounds_loop us vs ws m r (add k (Uint63.of_int (1))) d'
       else d'
  else d

(** val seed_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec seed_loop us vs ws d m j mk q tl =
  if bdec (ltb j m)
  then let du = get d (get us j) in
       let v = get vs j in
       if (&&)
            ((&&) (negb (eqb du iNF)) (ltsb (add du (get ws j)) (get d v)))
            (eqb (get mk v) (Uint63.of_int (0)))
       then seed_loop us vs ws d m (add j (Uint63.of_int (1)))
              (set mk v (Uint63.of_int (1))) (set q tl v)
              (add tl (Uint63.of_int (1)))
       else seed_loop us vs ws d m (add j (Uint63.of_int (1))) mk q tl
  else ((mk, q), tl)

(** val build_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec build_loop us m j hd nx =
  if bdec (ltb j m)
  then let u = get us j in
       let h = get hd u in
       build_loop us m (add j (Uint63.of_int (1)))
         (set hd u (add j (Uint63.of_int (1)))) (set nx j h)
  else (hd, nx)

(** val adj_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t **)

let rec adj_loop vs nx e mk q tl =
  if bdec (ltb (Uint63.of_int (0)) e)
  then let j = sub e (Uint63.of_int (1)) in
       let v = get vs j in
       let e' = get nx j in
       if bdec (ltb e' e)
       then if eqb (get mk v) (Uint63.of_int (0))
            then adj_loop vs nx e' (set mk v (Uint63.of_int (1)))
                   (set q tl v) (add tl (Uint63.of_int (1)))
            else adj_loop vs nx e' mk q tl
       else ((mk, q), tl)
  else ((mk, q), tl)

(** val bfs_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec bfs_loop vs hd nx n h mk q tl =
  if bdec (ltb h tl)
  then if bdec (ltb h n)
       then let x = get q h in
            let (p, tl') = adj_loop vs nx (get hd x) mk q tl in
            let (mk', q') = p in
            bfs_loop vs hd nx n (add h (Uint63.of_int (1))) mk' q' tl'
       else mk
  else mk

(** val answer_of :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t answer **)

let answer_of d mk t =
  let x = get d t in
  if eqb x iNF
  then Impossible
  else if eqb (get mk t) (Uint63.of_int (0)) then Dist x else MinusInfinity

(** val ans_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t answer Marray.t -> Uint63.t answer Marray.t **)

let rec ans_loop d mk qs q i out =
  if bdec (ltb i q)
  then let a = answer_of d mk (get qs i) in
       ans_loop d mk qs q (add i (Uint63.of_int (1))) (set out i a)
  else out

(** val shortestpath3_impl :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t answer Marray.t **)

let shortestpath3_impl n s us vs ws qs =
  let m = length us in
  let d0 = set (make n iNF) s (Uint63.of_int (0)) in
  let d =
    rounds_loop us vs ws m (sub n (Uint63.of_int (1))) (Uint63.of_int (0)) d0
  in
  let (p, tl) =
    seed_loop us vs ws d m (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (make n (Uint63.of_int (0))) (Uint63.of_int (0))
  in
  let (mk, q) = p in
  let (hd, nx) =
    build_loop us m (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (make m (Uint63.of_int (0)))
  in
  let mk' = bfs_loop vs hd nx n (Uint63.of_int (0)) mk q tl in
  let q0 = length qs in
  ans_loop d mk' qs q0 (Uint63.of_int (0)) (make q0 Impossible)

(** val shortestpath3 :
    uint -> uint -> uint Marray.t -> uint Marray.t -> sint Marray.t -> uint
    Marray.t -> sint answer Marray.t **)

let shortestpath3 =
  shortestpath3_impl
