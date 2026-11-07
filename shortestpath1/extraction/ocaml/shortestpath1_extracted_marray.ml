
(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

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

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (-1))

(** val count_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec count_loop us m k c =
  if bdec (ltb k m)
  then let u1 = add (get us k) (Uint63.of_int (1)) in
       count_loop us m (add k (Uint63.of_int (1)))
         (set c u1 (add (get c u1) (Uint63.of_int (1))))
  else c

(** val prefix_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec prefix_loop n i c =
  if bdec (ltb i n)
  then let a = get c i in
       let b = get c (add i (Uint63.of_int (1))) in
       prefix_loop n (add i (Uint63.of_int (1)))
         (set c (add i (Uint63.of_int (1))) (add b a))
  else c

(** val fill_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec fill_loop us vs ws m k pos adj wt =
  if bdec (ltb k m)
  then let u = get us k in
       let j = get pos u in
       fill_loop us vs ws m (add k (Uint63.of_int (1)))
         (set pos u (add j (Uint63.of_int (1)))) (set adj j (get vs k))
         (set wt j (get ws k))
  else (adj, wt)

(** val sift_up :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let rec sift_up hk hv i =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let p = lsr0 (sub i (Uint63.of_int (1))) (Uint63.of_int (1)) in
       let ki = get hk i in
       let kp = get hk p in
       if bdec (ltb ki kp)
       then let vi = get hv i in
            let vp = get hv p in
            sift_up (set (set hk i kp) p ki) (set (set hv i vp) p vi) p
       else (hk, hv)
  else (hk, hv)

(** val child : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let child hk sz l =
  if (&&) (ltb (add l (Uint63.of_int (1))) sz)
       (ltb (get hk (add l (Uint63.of_int (1)))) (get hk l))
  then add l (Uint63.of_int (1))
  else l

(** val sift_down :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let rec sift_down hk hv sz i =
  let l = add (add i i) (Uint63.of_int (1)) in
  if bdec ((&&) (ltb l sz) (ltb i l))
  then let c = child hk sz l in
       let ki = get hk i in
       let kc = get hk c in
       if bdec (ltb kc ki)
       then let vi = get hv i in
            let vc = get hv c in
            sift_down (set (set hk i kc) c ki) (set (set hv i vc) c vi) sz c
       else (hk, hv)
  else (hk, hv)

(** val pop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let pop hk hv sz =
  let sz' = sub sz (Uint63.of_int (1)) in
  let k = get hk sz' in
  let v = get hv sz' in
  sift_down (set hk (Uint63.of_int (0)) k) (set hv (Uint63.of_int (0)) v) sz'
    (Uint63.of_int (0))

(** val push :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let push hk hv sz k v =
  sift_up (set hk sz k) (set hv sz v) sz

type st = { st_dist : Uint63.t Marray.t; st_hk : Uint63.t Marray.t;
            st_hv : Uint63.t Marray.t; st_sz : Uint63.t }

(** val scan :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> st **)

let rec scan adj wt du hi j dist hk hv sz =
  if bdec (ltb j hi)
  then let v = get adj j in
       let nd = add du (get wt j) in
       if bdec (ltb nd (get dist v))
       then let (hk', hv') = push hk hv sz nd v in
            scan adj wt du hi (add j (Uint63.of_int (1))) (set dist v nd) hk'
              hv' (add sz (Uint63.of_int (1)))
       else scan adj wt du hi (add j (Uint63.of_int (1))) dist hk hv sz
  else { st_dist = dist; st_hk = hk; st_hv = hv; st_sz = sz }

(** val main :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> st -> Uint63.t Marray.t **)

let rec main off adj wt done0 st0 =
  if bdec (ltb (Uint63.of_int (0)) st0.st_sz)
  then let u = get st0.st_hv (Uint63.of_int (0)) in
       let (hk1, hv1) = pop st0.st_hk st0.st_hv st0.st_sz in
       if bdec
            ((&&) (ltb u (length done0))
              (eqb (get done0 u) (Uint63.of_int (0))))
       then let st2 =
              scan adj wt (get st0.st_dist u)
                (get off (add u (Uint63.of_int (1)))) (get off u) st0.st_dist
                hk1 hv1 (sub st0.st_sz (Uint63.of_int (1)))
            in
            main off adj wt (set done0 u (Uint63.of_int (1))) st2
       else main off adj wt done0 { st_dist = st0.st_dist; st_hk = hk1;
              st_hv = hv1; st_sz = (sub st0.st_sz (Uint63.of_int (1))) }
  else st0.st_dist

(** val out_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t option Marray.t ->
    Uint63.t option Marray.t **)

let rec out_loop dist n v out =
  if bdec (ltb v n)
  then let d = get dist v in
       out_loop dist n (add v (Uint63.of_int (1)))
         (set out v (if eqb d iNF then None else Some d))
  else out

(** val dijkstra_impl :
    uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint -> uint
    option Marray.t **)

let dijkstra_impl n us vs ws s =
  let m = length us in
  let c =
    count_loop us m (Uint63.of_int (0))
      (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))
  in
  let off = prefix_loop n (Uint63.of_int (0)) c in
  let (adj, wt) =
    fill_loop us vs ws m (Uint63.of_int (0)) (copy off)
      (make m (Uint63.of_int (0))) (make m (Uint63.of_int (0)))
  in
  let dist0 = set (make n iNF) s (Uint63.of_int (0)) in
  let hk0 = make (add m (Uint63.of_int (1))) (Uint63.of_int (0)) in
  let hv0 =
    set (make (add m (Uint63.of_int (1))) (Uint63.of_int (0)))
      (Uint63.of_int (0)) s
  in
  let dist =
    main off adj wt (make n (Uint63.of_int (0))) { st_dist = dist0; st_hk =
      hk0; st_hv = hv0; st_sz = (Uint63.of_int (1)) }
  in
  out_loop dist n (Uint63.of_int (0)) (make n None)

module Shortestpath1Impl =
 struct
  (** val dijkstra :
      uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint -> uint
      option Marray.t **)

  let dijkstra =
    dijkstra_impl
 end
