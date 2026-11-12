
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

(** val add_pipe :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let add_pipe m r a b c =
  let i1 = add (mul a m) b in
  let r1 = set r i1 (add (get r i1) c) in
  let i2 = add (mul b m) a in set r1 i2 (add (get r1 i2) c)

(** val init_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec init_loop pa pb pc m p j r =
  if bdec (ltb j p)
  then init_loop pa pb pc m p (add j (Uint63.of_int (1)))
         (add_pipe m r (get pa j) (get pb j) (get pc j))
  else r

(** val big : Uint63.t **)

let big =
  (Uint63.of_int (4611686018427387903))

(** val scan :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t **)

let rec scan r m u bu v par bott q tail =
  if bdec (ltb v m)
  then let x = get r (add (mul u m) v) in
       if (&&) (eqb (get par v) (Uint63.of_int (0)))
            (ltb (Uint63.of_int (0)) x)
       then scan r m u bu (add v (Uint63.of_int (1))) (set par v u)
              (set bott v (if ltb bu x then bu else x)) (set q tail v)
              (add tail (Uint63.of_int (1)))
       else scan r m u bu (add v (Uint63.of_int (1))) par bott q tail
  else (((par, bott), q), tail)

(** val bfs_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let rec bfs_loop r m head par bott q tail =
  if bdec (ltb head m)
  then if (&&) (ltb head tail)
            (eqb (get par (Uint63.of_int (2))) (Uint63.of_int (0)))
       then let u = get q head in
            let (p, tail') =
              scan r m u (get bott u) (Uint63.of_int (1)) par bott q tail
            in
            let (p0, q') = p in
            let (par', bott') = p0 in
            bfs_loop r m (add head (Uint63.of_int (1))) par' bott' q' tail'
       else (par, bott)
  else (par, bott)

(** val bfs :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let bfs r m =
  bfs_loop r m (Uint63.of_int (0))
    (set (make m (Uint63.of_int (0))) (Uint63.of_int (1)) (Uint63.of_int (1)))
    (set (make m (Uint63.of_int (0))) (Uint63.of_int (1)) big)
    (set (make m (Uint63.of_int (0))) (Uint63.of_int (0)) (Uint63.of_int (1)))
    (Uint63.of_int (1))

(** val walk :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec walk par m d r cur i =
  if bdec (ltb i m)
  then if eqb cur (Uint63.of_int (1))
       then r
       else let u = get par cur in
            let i1 = add (mul u m) cur in
            let r1 = set r i1 (sub (get r i1) d) in
            let i2 = add (mul cur m) u in
            let r2 = set r1 i2 (add (get r1 i2) d) in
            walk par m d r2 u (add i (Uint63.of_int (1)))
  else r

(** val augment :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t **)

let rec augment m b r val0 i =
  if bdec (ltb i b)
  then let (par, bott) = bfs r m in
       if eqb (get par (Uint63.of_int (2))) (Uint63.of_int (0))
       then (r, val0)
       else let d = get bott (Uint63.of_int (2)) in
            augment m b
              (walk par m d r (Uint63.of_int (2)) (Uint63.of_int (0)))
              (add val0 d) (add i (Uint63.of_int (1)))
  else (r, val0)

(** val budget : Uint63.t **)

let budget =
  (Uint63.of_int (1099511627776))

(** val imp_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec imp_loop ia ib ic m k t r val0 out =
  if bdec (ltb t k)
  then let r1 = add_pipe m r (get ia t) (get ib t) (get ic t) in
       let (r2, val2) = augment m budget r1 val0 (Uint63.of_int (0)) in
       imp_loop ia ib ic m k (add t (Uint63.of_int (1))) r2 val2
         (set out (add t (Uint63.of_int (1))) val2)
  else out

(** val water_impl :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let water_impl n pa pb pc ia ib ic =
  let m = add n (Uint63.of_int (1)) in
  let p = length pa in
  let r =
    init_loop pa pb pc m p (Uint63.of_int (0))
      (make (mul m m) (Uint63.of_int (0)))
  in
  let (r1, v0) = augment m budget r (Uint63.of_int (0)) (Uint63.of_int (0)) in
  let k = length ia in
  imp_loop ia ib ic m k (Uint63.of_int (0)) r1 v0
    (set (make (add k (Uint63.of_int (1))) (Uint63.of_int (0)))
      (Uint63.of_int (0)) v0)

(** val water :
    uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t
    -> uint Marray.t -> uint Marray.t -> uint Marray.t **)

let water =
  water_impl
