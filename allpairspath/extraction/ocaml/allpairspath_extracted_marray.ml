
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

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

type 'a answer =
| Impossible
| NegInfinity
| Distance of 'a

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val for_acc :
    (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let rec for_acc f hi i s =
  if bdec (ltb i hi)
  then for_acc f hi (add i (Uint63.of_int (1))) (f i s)
  else s

(** val for_loop :
    (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let for_loop f lo hi s =
  for_acc f hi lo s

(** val swap :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let swap t i j =
  let a = get t i in let b = get t j in set (set t i b) j a

(** val sift_up : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let rec sift_up t i =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let p = div (sub i (Uint63.of_int (1))) (Uint63.of_int (2)) in
       if ltb (get t i) (get t p) then sift_up (swap t i p) p else t
  else t

(** val sift_down :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec sift_down t s i =
  let l = add (mul (Uint63.of_int (2)) i) (Uint63.of_int (1)) in
  if ltb l s
  then let r = add l (Uint63.of_int (1)) in
       let c = if (&&) (ltb r s) (ltb (get t r) (get t l)) then r else l in
       if bdec ((&&) (ltb i c) (ltb c s))
       then if ltb (get t c) (get t i) then sift_down (swap t i c) s c else t
       else t
  else t

(** val hpush :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let hpush t s x =
  sift_up (set t s x) s

(** val hpop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t * Uint63.t Marray.t **)

let hpop t s =
  let top = get t (Uint63.of_int (0)) in
  let s' = sub s (Uint63.of_int (1)) in
  let last = get t s' in
  (top, (sift_down (set t (Uint63.of_int (0)) last) s' (Uint63.of_int (0))))

(** val adj_step :
    Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t)
    -> Uint63.t Marray.t * Uint63.t Marray.t **)

let adj_step us k = function
| (hd, nx) ->
  let a = get us k in
  let old = get hd a in
  let nx' = set nx k old in
  let hd' = set hd a (add k (Uint63.of_int (1))) in (hd', nx')

(** val build_adj :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t
    Marray.t **)

let build_adj n m us =
  for_loop (adj_step us) (Uint63.of_int (0)) m ((make n (Uint63.of_int (0))),
    (make m (Uint63.of_int (0))))

(** val chain_acc :
    Uint63.t Marray.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

let rec chain_acc nx f cur s =
  if bdec (ltb (Uint63.of_int (0)) cur)
  then let e = sub cur (Uint63.of_int (1)) in
       let s' = f e s in
       let c' = get nx e in
       if bdec (ltb c' cur) then chain_acc nx f c' s' else s'
  else s

(** val chain_fold :
    Uint63.t Marray.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

let chain_fold =
  chain_acc

(** val bfs_visit :
    Uint63.t Marray.t -> Uint63.t -> ((bool Marray.t * Uint63.t
    Marray.t) * Uint63.t) -> (bool Marray.t * Uint63.t Marray.t) * Uint63.t **)

let bfs_visit vs e st = match st with
| (p, tl) ->
  let (mark, q) = p in
  let b = get vs e in
  if get mark b
  then st
  else (((set mark b true), (set q tl b)), (add tl (Uint63.of_int (1))))

(** val bfs_acc :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> ((bool Marray.t * Uint63.t Marray.t) * Uint63.t) -> bool
    Marray.t **)

let rec bfs_acc hd nx vs cap h st = match st with
| (p, tl) ->
  let (mark, q) = p in
  if bdec ((&&) (ltb h tl) (ltb h cap))
  then let x = get q h in
       bfs_acc hd nx vs cap (add h (Uint63.of_int (1)))
         (chain_fold nx (bfs_visit vs) (get hd x) st)
  else mark

(** val seed_step :
    bool Marray.t -> Uint63.t -> ((bool Marray.t * Uint63.t
    Marray.t) * Uint63.t) -> (bool Marray.t * Uint63.t Marray.t) * Uint63.t **)

let seed_step seed a st = match st with
| (p, tl) ->
  let (mark, q) = p in
  if get seed a
  then (((set mark a true), (set q tl a)), (add tl (Uint63.of_int (1))))
  else st

(** val closure :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> bool Marray.t -> bool Marray.t **)

let closure n hd nx vs seed =
  let st0 =
    for_loop (seed_step seed) (Uint63.of_int (0)) n (((make n false),
      (make n (Uint63.of_int (0)))), (Uint63.of_int (0)))
  in
  bfs_acc hd nx vs n (Uint63.of_int (0)) st0

(** val copy_step :
    Uint63.t -> Uint63.t -> bool Marray.t -> Uint63.t -> bool Marray.t ->
    bool Marray.t **)

let copy_step n s row v r =
  set r (add (mul s n) v) (get row v)

(** val reach_row :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> bool Marray.t -> bool Marray.t **)

let reach_row n hd nx vs s r =
  let row = closure n hd nx vs (set (make n false) s true) in
  for_loop (copy_step n s row) (Uint63.of_int (0)) n r

(** val reach_matrix :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> bool Marray.t **)

let reach_matrix n hd nx vs =
  for_loop (reach_row n hd nx vs) (Uint63.of_int (0)) n (make (mul n n) false)

(** val bf_edge :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t
    -> bool) -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let bf_edge us vs ws keep k h =
  if keep k
  then let a = get us k in
       let b = get vs k in
       let nb = add (get h a) (get ws k) in
       if ltsb nb (get h b) then set h b nb else h
  else h

(** val bf_round :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> (Uint63.t -> bool) -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t **)

let bf_round m us vs ws keep _ h =
  for_loop (bf_edge us vs ws keep) (Uint63.of_int (0)) m h

(** val bf :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> (Uint63.t -> bool) -> Uint63.t Marray.t **)

let bf n m us vs ws keep =
  for_loop (bf_round m us vs ws keep) (Uint63.of_int (0)) n
    (make n (Uint63.of_int (0)))

(** val bad_step :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> bool Marray.t ->
    bool Marray.t **)

let bad_step n us vs ws r h k bad =
  let a = get us k in
  let b = get vs k in
  if (&&) (get r (add (mul b n) a))
       (ltsb (add (get h a) (get ws k)) (get h b))
  then set bad a true
  else bad

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (1073741824))

(** val relax :
    Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> bool Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t) -> (Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t **)

let relax vs ws bad done0 p v d e st = match st with
| (p0, sz) ->
  let (d0, hp) = p0 in
  let b = get vs e in
  if (&&) (negb (get bad b)) (negb (get done0 b))
  then let nd = sub (add (add d (get ws e)) (get p v)) (get p b) in
       if ltb nd (get d0 b)
       then (((set d0 b nd),
              (hpush hp sz (add (mul nd (Uint63.of_int (256))) b))),
              (add sz (Uint63.of_int (1))))
       else st
  else st

(** val dij_body :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> bool Marray.t -> Uint63.t Marray.t -> (((Uint63.t
    Marray.t * bool Marray.t) * Uint63.t Marray.t) * Uint63.t) -> ((Uint63.t
    Marray.t * bool Marray.t) * Uint63.t Marray.t) * Uint63.t **)

let dij_body hd nx vs ws bad p = function
| (p0, sz) ->
  let (p1, hp) = p0 in
  let (d, done0) = p1 in
  let (top, hp1) = hpop hp sz in
  let sz1 = sub sz (Uint63.of_int (1)) in
  let v = mod0 top (Uint63.of_int (256)) in
  let d0 = div top (Uint63.of_int (256)) in
  if get done0 v
  then (((d, done0), hp1), sz1)
  else let done' = set done0 v true in
       let d' = set d v d0 in
       if get bad v
       then (((d', done'), hp1), sz1)
       else let (p2, sz2) =
              chain_fold nx (relax vs ws bad done' p v d0) (get hd v) ((d',
                hp1), sz1)
            in
            let (d2, hp2) = p2 in (((d2, done'), hp2), sz2)

(** val dij_acc :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    (((Uint63.t Marray.t * bool Marray.t) * Uint63.t Marray.t) * Uint63.t) ->
    Uint63.t Marray.t **)

let rec dij_acc hd nx vs ws bad p lim steps st = match st with
| (p0, sz) ->
  let (p1, _) = p0 in
  let (d, _) = p1 in
  if bdec ((&&) (ltb (Uint63.of_int (0)) sz) (ltb steps lim))
  then dij_acc hd nx vs ws bad p lim (add steps (Uint63.of_int (1)))
         (dij_body hd nx vs ws bad p st)
  else d

(** val dijkstra :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let dijkstra n m hd nx vs ws bad p u =
  let d0 = set (make n iNF) u (Uint63.of_int (0)) in
  let hp0 =
    set (make (add m (Uint63.of_int (1))) (Uint63.of_int (0)))
      (Uint63.of_int (0)) u
  in
  dij_acc hd nx vs ws bad p (add m (Uint63.of_int (1))) (Uint63.of_int (0))
    (((d0, (make n false)), hp0), (Uint63.of_int (1)))

(** val cell :
    Uint63.t -> bool Marray.t -> bool Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t answer **)

let cell n r neg d p u v =
  if get neg v
  then NegInfinity
  else if get r (add (mul u n) v)
       then Distance (add (sub (get d v) (get p u)) (get p v))
       else Impossible

(** val negseed_step :
    Uint63.t -> bool Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t ->
    bool Marray.t -> bool Marray.t **)

let negseed_step n r bad u a s =
  if (&&) (get bad a) (get r (add (mul u n) a)) then set s a true else s

(** val row_of :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> bool Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> Uint63.t answer Marray.t **)

let row_of n m hd nx vs ws r bad p u =
  let seed =
    for_loop (negseed_step n r bad u) (Uint63.of_int (0)) n (make n false)
  in
  let neg = closure n hd nx vs seed in
  let d = dijkstra n m hd nx vs ws bad p u in
  for_loop (fun v r0 -> set r0 v (cell n r neg d p u v)) (Uint63.of_int (0))
    n (make n Impossible)

(** val allpairspath_impl :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t answer Marray.t Marray.t **)

let allpairspath_impl n us vs ws =
  let m = length us in
  let (hd, nx) = build_adj n m us in
  let r = reach_matrix n hd nx vs in
  let h1 =
    bf n m us vs ws (fun k -> get r (add (mul (get vs k) n) (get us k)))
  in
  let bad =
    for_loop (bad_step n us vs ws r h1) (Uint63.of_int (0)) m (make n false)
  in
  let p =
    bf n m us vs ws (fun k ->
      (&&) (negb (get bad (get us k))) (negb (get bad (get vs k))))
  in
  for_loop (fun u res -> set res u (row_of n m hd nx vs ws r bad p u))
    (Uint63.of_int (0)) n (make n (make (Uint63.of_int (0)) Impossible))

module AllpairspathImpl =
 struct
  (** val allpairspath :
      uint -> uint Marray.t -> uint Marray.t -> sint Marray.t -> sint answer
      Marray.t Marray.t **)

  let allpairspath =
    allpairspath_impl
 end
