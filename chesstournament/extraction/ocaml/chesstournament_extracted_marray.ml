
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

(** val find :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t **)

let rec find p x =
  let y = get p x in
  if bdec (eqb y x)
  then (p, x)
  else let f = find p y in ((set (fst f) x (snd f)), (snd f))

(** val union :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let union p rk a b =
  if eqb a b
  then (p, rk)
  else let ra = get rk a in
       let rb = get rk b in
       if ltb ra rb
       then ((set p a b), rk)
       else if ltb rb ra
            then ((set p b a), rk)
            else ((set p b a), (set rk a (add ra (Uint63.of_int (1)))))

(** val unite :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let unite p rk k l =
  let f1 = find p k in
  let f2 = find (fst f1) l in union (fst f2) rk (snd f1) (snd f2)

(** val iota_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec iota_loop n x p =
  if bdec (ltb x n)
  then iota_loop n (add x (Uint63.of_int (1))) (set p x x)
  else p

(** val iota : Uint63.t -> Uint63.t Marray.t **)

let iota n =
  iota_loop n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))

(** val uf_loop :
    Uint63.t Marray.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec uf_loop ks wins ls m j p rk =
  if bdec (ltb j m)
  then if get wins j
       then uf_loop ks wins ls m (add j (Uint63.of_int (1))) p rk
       else let u = unite p rk (get ks j) (get ls j) in
            uf_loop ks wins ls m (add j (Uint63.of_int (1))) (fst u) (snd u)
  else p

(** val rep_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec rep_loop n x p rep =
  if bdec (ltb x n)
  then let f = find p x in
       rep_loop n (add x (Uint63.of_int (1))) (fst f) (set rep x (snd f))
  else rep

(** val deg_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec deg_loop rep ks wins ls m j od id =
  if bdec (ltb j m)
  then if get wins j
       then let a = get rep (get ks j) in
            let b = get rep (get ls j) in
            deg_loop rep ks wins ls m (add j (Uint63.of_int (1)))
              (set od a (add (get od a) (Uint63.of_int (1))))
              (set id b (add (get id b) (Uint63.of_int (1))))
       else deg_loop rep ks wins ls m (add j (Uint63.of_int (1))) od id
  else (od, id)

(** val pre_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec pre_loop od n u s st pos =
  if bdec (ltb u n)
  then let s' = add s (get od u) in
       pre_loop od n (add u (Uint63.of_int (1))) s'
         (set st (add u (Uint63.of_int (1))) s') (set pos u s)
  else (st, pos)

(** val fill_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec fill_loop rep ks wins ls m j pos adj =
  if bdec (ltb j m)
  then if get wins j
       then let a = get rep (get ks j) in
            let pa = get pos a in
            fill_loop rep ks wins ls m (add j (Uint63.of_int (1)))
              (set pos a (add pa (Uint63.of_int (1))))
              (set adj pa (get rep (get ls j)))
       else fill_loop rep ks wins ls m (add j (Uint63.of_int (1))) pos adj
  else adj

(** val init_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t * Uint63.t **)

let rec init_loop id n v q t =
  if bdec (ltb v n)
  then if eqb (get id v) (Uint63.of_int (0))
       then init_loop id n (add v (Uint63.of_int (1))) (set q t v)
              (add t (Uint63.of_int (1)))
       else init_loop id n (add v (Uint63.of_int (1))) q t
  else (q, t)

(** val inner :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t **)

let rec inner adj hi e d q t =
  if bdec (ltb e hi)
  then let v = get adj e in
       let dv = sub (get d v) (Uint63.of_int (1)) in
       if eqb dv (Uint63.of_int (0))
       then inner adj hi (add e (Uint63.of_int (1))) (set d v dv) (set q t v)
              (add t (Uint63.of_int (1)))
       else inner adj hi (add e (Uint63.of_int (1))) (set d v dv) q t
  else ((d, q), t)

(** val kahn :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let rec kahn adj st h d q t =
  if bdec (ltb h t)
  then let u = get q h in
       let r = inner adj (get st (add u (Uint63.of_int (1)))) (get st u) d q t
       in
       kahn adj st (add h (Uint63.of_int (1))) (fst (fst r)) (snd (fst r))
         (snd r)
  else t

(** val chess_impl :
    uint -> uint Marray.t -> bool Marray.t -> uint Marray.t -> bool **)

let chess_impl n ks wins ls =
  let m = length ks in
  let p0 = iota n in
  let p1 =
    uf_loop ks wins ls m (Uint63.of_int (0)) p0 (make n (Uint63.of_int (0)))
  in
  let rep = rep_loop n (Uint63.of_int (0)) p1 (make n (Uint63.of_int (0))) in
  let dg =
    deg_loop rep ks wins ls m (Uint63.of_int (0))
      (make n (Uint63.of_int (0))) (make n (Uint63.of_int (0)))
  in
  let sp =
    pre_loop (fst dg) n (Uint63.of_int (0)) (Uint63.of_int (0))
      (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))
      (make n (Uint63.of_int (0)))
  in
  let adj =
    fill_loop rep ks wins ls m (Uint63.of_int (0)) (snd sp)
      (make m (Uint63.of_int (0)))
  in
  let qi =
    init_loop (snd dg) n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (Uint63.of_int (0))
  in
  let t = kahn adj (fst sp) (Uint63.of_int (0)) (snd dg) (fst qi) (snd qi) in
  eqb t n

(** val chess_consistent :
    uint -> uint Marray.t -> bool Marray.t -> uint Marray.t -> bool **)

let chess_consistent =
  chess_impl
