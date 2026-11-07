
(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

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

type command =
| Add of uint * uint
| Query of uint

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val nil : Uint63.t **)

let nil =
  (Uint63.of_int (-1))

(** val kl : Uint63.t -> Uint63.t **)

let kl k =
  lsr0 k (Uint63.of_int (1))

(** val kh : Uint63.t -> Uint63.t **)

let kh k =
  sub k (lsr0 k (Uint63.of_int (1)))

(** val clb :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let clb t b k i =
  add (add (add b (Uint63.of_int (2))) (get t (kh k))) (mul i (get t (kl k)))

(** val vins :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec vins t v b k x =
  let m = get v b in
  if eqb m nil
  then set (set v b x) (add b (Uint63.of_int (1))) x
  else let y = if ltb x m then m else x in
       let v1 = if ltb x m then set v b x else v in
       let v2 =
         if bdec (ltb (Uint63.of_int (1)) k)
         then let hy = lsr0 y (kl k) in
              let ly = sub y (lsl0 hy (kl k)) in
              let c = clb t b k hy in
              if eqb (get v1 c) nil
              then let v3 = vins t v1 (add b (Uint63.of_int (2))) (kh k) hy in
                   set (set v3 c ly) (add c (Uint63.of_int (1))) ly
              else vins t v1 c (kl k) ly
         else v1
       in
       if ltb (get v2 (add b (Uint63.of_int (1)))) y
       then set v2 (add b (Uint63.of_int (1))) y
       else v2

(** val vdel :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec vdel t v b k x =
  let m = get v b in
  let m0 = get v (add b (Uint63.of_int (1))) in
  if eqb m m0
  then set (set v b nil) (add b (Uint63.of_int (1))) nil
  else if bdec (ltb (Uint63.of_int (1)) k)
       then let y =
              if eqb x m
              then let f = get v (add b (Uint63.of_int (2))) in
                   add (lsl0 f (kl k)) (get v (clb t b k f))
              else x
            in
            let v1 = if eqb x m then set v b y else v in
            let hy = lsr0 y (kl k) in
            let ly = sub y (lsl0 hy (kl k)) in
            let c = clb t b k hy in
            let v2 = vdel t v1 c (kl k) ly in
            if eqb (get v2 c) nil
            then let v3 = vdel t v2 (add b (Uint63.of_int (2))) (kh k) hy in
                 if eqb y (get v3 (add b (Uint63.of_int (1))))
                 then let sm =
                        get v3
                          (add (add b (Uint63.of_int (2)))
                            (Uint63.of_int (1)))
                      in
                      if eqb sm nil
                      then set v3 (add b (Uint63.of_int (1))) (get v3 b)
                      else set v3 (add b (Uint63.of_int (1)))
                             (add (lsl0 sm (kl k))
                               (get v3
                                 (add (clb t b k sm) (Uint63.of_int (1)))))
                 else v3
            else if eqb y (get v2 (add b (Uint63.of_int (1))))
                 then set v2 (add b (Uint63.of_int (1)))
                        (add (lsl0 hy (kl k))
                          (get v2 (add c (Uint63.of_int (1)))))
                 else v2
       else let r =
              if eqb x (Uint63.of_int (0))
              then (Uint63.of_int (1))
              else (Uint63.of_int (0))
            in
            set (set v b r) (add b (Uint63.of_int (1))) r

(** val vpred :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec vpred t v b k x =
  let m = get v b in
  if ltb x m
  then nil
  else let m0 = get v (add b (Uint63.of_int (1))) in
       if leb m0 x
       then m0
       else if bdec (ltb (Uint63.of_int (1)) k)
            then let hx = lsr0 x (kl k) in
                 let lx = sub x (lsl0 hx (kl k)) in
                 let c = clb t b k hx in
                 if leb (get v c) lx
                 then add (lsl0 hx (kl k)) (vpred t v c (kl k) lx)
                 else if eqb hx (Uint63.of_int (0))
                      then m
                      else let ph =
                             vpred t v (add b (Uint63.of_int (2))) (kh k)
                               (sub hx (Uint63.of_int (1)))
                           in
                           if eqb ph nil
                           then m
                           else add (lsl0 ph (kl k))
                                  (get v
                                    (add (clb t b k ph) (Uint63.of_int (1))))
            else m

(** val sup :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec sup gd s i =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let p = lsr0 (sub i (Uint63.of_int (1))) (Uint63.of_int (1)) in
       let a = get gd (add s p) in
       let b = get gd (add s i) in
       if ltb a b then sup (set (set gd (add s p) b) (add s i) a) s p else gd
  else gd

(** val pickc :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let pickc gd s n i =
  let c1 = add (mul (Uint63.of_int (2)) i) (Uint63.of_int (1)) in
  if ltb (add c1 (Uint63.of_int (1))) n
  then if ltb (get gd (add s c1))
            (get gd (add s (add c1 (Uint63.of_int (1)))))
       then add c1 (Uint63.of_int (1))
       else c1
  else c1

(** val sdown :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec sdown gd s n i =
  if bdec
       ((&&) (ltb i (add (mul (Uint63.of_int (2)) i) (Uint63.of_int (1))))
         (ltb (add (mul (Uint63.of_int (2)) i) (Uint63.of_int (1))) n))
  then let c = pickc gd s n i in
       let a = get gd (add s i) in
       let b = get gd (add s c) in
       if ltb a b
       then sdown (set (set gd (add s i) b) (add s c) a) s n c
       else gd
  else gd

(** val hpush :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let hpush gd s n g =
  sup (set gd (add s n) g) s n

(** val hpop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let hpop gd s n =
  let last = get gd (add s (sub n (Uint63.of_int (1)))) in
  sdown (set gd s last) s (sub n (Uint63.of_int (1))) (Uint63.of_int (0))

(** val scan :
    command Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec scan x n j m q =
  if bdec (ltb j n)
  then (match get x j with
        | Add (e, _) ->
          scan x n (add j (Uint63.of_int (1))) (if ltb m e then e else m) q
        | Query _ ->
          scan x n (add j (Uint63.of_int (1))) m (add q (Uint63.of_int (1))))
  else (m, q)

(** val kloop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec kloop m k =
  if bdec
       ((&&) (ltb k (Uint63.of_int (62)))
         (leb (lsl0 (Uint63.of_int (1)) k) m))
  then kloop m (add k (Uint63.of_int (1)))
  else k

(** val stab :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec stab t k k0 =
  if bdec (ltb k0 (add k (Uint63.of_int (1))))
  then let s =
         if leb k0 (Uint63.of_int (1))
         then (Uint63.of_int (2))
         else add (add (Uint63.of_int (2)) (get t (kh k0)))
                (lsl0 (get t (kl k0)) (kh k0))
       in
       stab (set t k0 s) k (add k0 (Uint63.of_int (1)))
  else t

(** val cntloop :
    command Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t **)

let rec cntloop x n j c =
  if bdec (ltb j n)
  then (match get x j with
        | Add (e, _) ->
          cntloop x n (add j (Uint63.of_int (1)))
            (set c e (add (get c e) (Uint63.of_int (1))))
        | Query _ -> cntloop x n (add j (Uint63.of_int (1))) c)
  else c

(** val pref :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec pref c u e acc =
  if bdec (ltb e u)
  then let ce = get c e in
       pref (set c e acc) u (add e (Uint63.of_int (1))) (add acc ce)
  else c

(** val sess :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t **)

let rec sess t st k u v gd hz x acc =
  let x' = if ltb x u then x else sub u (Uint63.of_int (1)) in
  let e = vpred t v (Uint63.of_int (0)) k x' in
  if bdec ((&&) (ltb (Uint63.of_int (0)) e) (leb e x))
  then let s = get st e in
       let n = get hz e in
       let g = get gd s in
       let gd1 = hpop gd s n in
       let hz1 = set hz e (sub n (Uint63.of_int (1))) in
       let v1 =
         if eqb n (Uint63.of_int (1))
         then vdel t v (Uint63.of_int (0)) k e
         else v
       in
       sess t st k u v1 gd1 hz1 (sub x e) (add acc g)
  else (((v, gd), hz), acc)

(** val mloop :
    command Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec mloop x t st k u n j v gd hz out qi =
  if bdec (ltb j n)
  then (match get x j with
        | Add (e, g) ->
          let s = get st e in
          let n0 = get hz e in
          let gd1 = hpush gd s n0 g in
          let hz1 = set hz e (add n0 (Uint63.of_int (1))) in
          let v1 =
            if eqb n0 (Uint63.of_int (0))
            then vins t v (Uint63.of_int (0)) k e
            else v
          in
          mloop x t st k u n (add j (Uint63.of_int (1))) v1 gd1 hz1 out qi
        | Query q ->
          let (p, a) = sess t st k u v gd hz q (Uint63.of_int (0)) in
          let (p0, hz1) = p in
          let (v1, gd1) = p0 in
          mloop x t st k u n (add j (Uint63.of_int (1))) v1 gd1 hz1
            (set out qi a) (add qi (Uint63.of_int (1))))
  else out

(** val kattissquest_impl : command Marray.t -> uint Marray.t **)

let kattissquest_impl x =
  let n = length x in
  let (mE, q) =
    scan x n (Uint63.of_int (0)) (Uint63.of_int (1)) (Uint63.of_int (0))
  in
  let k = kloop mE (Uint63.of_int (1)) in
  let t =
    stab (make (add k (Uint63.of_int (1))) (Uint63.of_int (0))) k
      (Uint63.of_int (1))
  in
  let u = lsl0 (Uint63.of_int (1)) k in
  let cnt = cntloop x n (Uint63.of_int (0)) (make u (Uint63.of_int (0))) in
  let st = pref cnt u (Uint63.of_int (0)) (Uint63.of_int (0)) in
  mloop x t st k u n (Uint63.of_int (0)) (make (get t k) nil)
    (make n (Uint63.of_int (0))) (make u (Uint63.of_int (0)))
    (make q (Uint63.of_int (0))) (Uint63.of_int (0))

module KattissquestImpl =
 struct
  (** val kattissquest : command Marray.t -> uint Marray.t **)

  let kattissquest =
    kattissquest_impl
 end
