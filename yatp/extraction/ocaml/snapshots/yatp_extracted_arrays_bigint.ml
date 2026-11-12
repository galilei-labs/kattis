
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

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (-4611686018427387904))

(** val max_loop :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec max_loop a n i acc =
  if bdec (ltb i n)
  then max_loop a n (add i (Uint63.of_int (1)))
         (if ltb acc ((fun a i -> Array.unsafe_get a (Uint63.hash i)) a i)
          then (fun a i -> Array.unsafe_get a (Uint63.hash i)) a i
          else acc)
  else acc

(** val true_loop : Uint63.t -> Uint63.t -> bool array -> bool array **)

let rec true_loop n1 i a =
  if bdec (ltb i n1)
  then true_loop n1 (add i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a i true)
  else a

(** val hsrc : Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t **)

let hsrc xu xv h =
  if eqb (mod0 h (Uint63.of_int (2))) (Uint63.of_int (0))
  then (fun a i -> Array.unsafe_get a (Uint63.hash i)) xu
         (div h (Uint63.of_int (2)))
  else (fun a i -> Array.unsafe_get a (Uint63.hash i)) xv
         (div h (Uint63.of_int (2)))

(** val hdst : Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t **)

let hdst xu xv h =
  if eqb (mod0 h (Uint63.of_int (2))) (Uint63.of_int (0))
  then (fun a i -> Array.unsafe_get a (Uint63.hash i)) xv
         (div h (Uint63.of_int (2)))
  else (fun a i -> Array.unsafe_get a (Uint63.hash i)) xu
         (div h (Uint63.of_int (2)))

(** val deg_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t
    array -> Uint63.t array **)

let rec deg_loop xu xv hh h deg =
  if bdec (ltb h hh)
  then let x = hsrc xu xv h in
       deg_loop xu xv hh (add h (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) deg x
           (add ((fun a i -> Array.unsafe_get a (Uint63.hash i)) deg x)
             (Uint63.of_int (1))))
  else deg

(** val start_loop :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t
    array -> Uint63.t array * Uint63.t array **)

let rec start_loop deg n1 x sa pos =
  if bdec (ltb x n1)
  then let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) sa x in
       start_loop deg n1 (add x (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) sa
           (add x (Uint63.of_int (1)))
           (add s ((fun a i -> Array.unsafe_get a (Uint63.hash i)) deg x)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) pos x s)
  else (sa, pos)

(** val fill_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t ->
    Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t array * Uint63.t array **)

let rec fill_loop xu xv xw hh h pos nbr wt =
  if bdec (ltb h hh)
  then let x = hsrc xu xv h in
       let i = (fun a i -> Array.unsafe_get a (Uint63.hash i)) pos x in
       fill_loop xu xv xw hh (add h (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) pos x
           (add i (Uint63.of_int (1))))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) nbr i
           (hdst xu xv h))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) wt i
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xw
             (div h (Uint63.of_int (2)))))
  else (nbr, wt)

type bst = { b_vis : Uint63.t array; b_comp : Uint63.t array;
             b_par : Uint63.t array; b_d : Uint63.t array; b_tail : Uint63.t;
             b_flag : bool }

(** val scan_step :
    bool array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    bst -> bst **)

let scan_step alive s x dx y w b =
  if (fun a i -> Array.unsafe_get a (Uint63.hash i)) alive y
  then if eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) b.b_vis y) s
       then { b_vis = b.b_vis; b_comp = b.b_comp; b_par = b.b_par; b_d =
              b.b_d; b_tail = b.b_tail; b_flag =
              ((&&) b.b_flag
                (leb
                  ((fun a i -> Array.unsafe_get a (Uint63.hash i)) b.b_d y)
                  (add dx w))) }
       else { b_vis =
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) b.b_vis
                y s);
              b_comp =
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                b.b_comp b.b_tail y);
              b_par =
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) b.b_par
                y x);
              b_d =
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) b.b_d y
                (add dx w));
              b_tail = (add b.b_tail (Uint63.of_int (1))); b_flag = b.b_flag }
  else b

(** val scan_loop :
    Uint63.t array -> Uint63.t array -> bool array -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> bst -> bst **)

let rec scan_loop nbr wt alive s x dx e j b =
  if bdec (ltb j e)
  then scan_loop nbr wt alive s x dx e (add j (Uint63.of_int (1)))
         (scan_step alive s x dx
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) nbr j)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) wt j) b)
  else b

(** val bfs_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
    Uint63.t -> Uint63.t -> Uint63.t -> bst -> bst **)

let rec bfs_loop sa nbr wt alive s l head b =
  if bdec (ltb head b.b_tail)
  then if bdec (ltb head l)
       then let x =
              (fun a i -> Array.unsafe_get a (Uint63.hash i)) b.b_comp head
            in
            bfs_loop sa nbr wt alive s l (add head (Uint63.of_int (1)))
              (scan_loop nbr wt alive s x
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) b.b_d x)
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) sa
                  (add x (Uint63.of_int (1))))
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) sa x) b)
       else b
  else b

(** val bfs_init :
    Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t
    array -> Uint63.t array -> bst **)

let bfs_init s root vis comp par d =
  { b_vis =
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) vis root s);
    b_comp =
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) comp
      (Uint63.of_int (0)) root);
    b_par =
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) par root root);
    b_d =
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) d root
      (Uint63.of_int (0)));
    b_tail = (Uint63.of_int (1)); b_flag = true }

(** val bfs :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
    Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t
    array -> Uint63.t array -> bst **)

let bfs sa nbr wt alive s root vis comp par d =
  bfs_loop sa nbr wt alive s ((fun a -> Uint63.of_int (Array.length a)) comp)
    (Uint63.of_int (0)) (bfs_init s root vis comp par d)

(** val rscan :
    Uint63.t array -> Uint63.t array -> bool array -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t array -> bool -> Uint63.t array * bool **)

let rec rscan nbr wt alive dx e j d ch =
  if bdec (ltb j e)
  then let y = (fun a i -> Array.unsafe_get a (Uint63.hash i)) nbr j in
       let nv = add dx ((fun a i -> Array.unsafe_get a (Uint63.hash i)) wt j)
       in
       if (&&)
            ((&&) ((fun a i -> Array.unsafe_get a (Uint63.hash i)) alive y)
              (ltb y ((fun a -> Uint63.of_int (Array.length a)) d)))
            (ltb nv ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d y))
       then rscan nbr wt alive dx e (add j (Uint63.of_int (1)))
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) d y nv)
              true
       else rscan nbr wt alive dx e (add j (Uint63.of_int (1))) d ch
  else (d, ch)

(** val rpass :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> bool ->
    Uint63.t array * bool **)

let rec rpass sa nbr wt alive comp t i d ch =
  if bdec (ltb i t)
  then let x = (fun a i -> Array.unsafe_get a (Uint63.hash i)) comp i in
       let r =
         rscan nbr wt alive
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d x)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) sa
             (add x (Uint63.of_int (1))))
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) sa x) d ch
       in
       rpass sa nbr wt alive comp t (add i (Uint63.of_int (1))) (fst r)
         (snd r)
  else (d, ch)

(** val rloop :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
    Uint63.t array -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let rec rloop sa nbr wt alive comp t d =
  let pr = rpass sa nbr wt alive comp t (Uint63.of_int (0)) d false in
  if bdec (snd pr) then rloop sa nbr wt alive comp t (fst pr) else fst pr

(** val relax :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
    Uint63.t array -> Uint63.t -> bst -> Uint63.t array **)

let relax sa nbr wt alive comp t b =
  if b.b_flag then b.b_d else rloop sa nbr wt alive comp t b.b_d

(** val sz_init :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t
    array -> Uint63.t array * Uint63.t array **)

let rec sz_init comp t i sz big =
  if bdec (ltb i t)
  then let x = (fun a i -> Array.unsafe_get a (Uint63.hash i)) comp i in
       sz_init comp t (add i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) sz x
           (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) big x
           (Uint63.of_int (0)))
  else (sz, big)

(** val sz_acc :
    Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t array ->
    Uint63.t array -> Uint63.t array * Uint63.t array **)

let rec sz_acc comp par i sz big =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let x = (fun a i -> Array.unsafe_get a (Uint63.hash i)) comp i in
       let p = (fun a i -> Array.unsafe_get a (Uint63.hash i)) par x in
       let v = (fun a i -> Array.unsafe_get a (Uint63.hash i)) sz x in
       sz_acc comp par (sub i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) sz p
           (add ((fun a i -> Array.unsafe_get a (Uint63.hash i)) sz p) v))
         (if ltb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) big p) v
          then (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) big p v
          else big)
  else (sz, big)

(** val argmin :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec argmin comp sz big t i bi bv =
  if bdec (ltb i t)
  then let x = (fun a i -> Array.unsafe_get a (Uint63.hash i)) comp i in
       let up = sub t ((fun a i -> Array.unsafe_get a (Uint63.hash i)) sz x)
       in
       let v =
         if ltb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) big x) up
         then up
         else (fun a i -> Array.unsafe_get a (Uint63.hash i)) big x
       in
       if ltb v bv
       then argmin comp sz big t (add i (Uint63.of_int (1))) i v
       else argmin comp sz big t (add i (Uint63.of_int (1))) bi bv
  else bi

(** val centroid :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t -> Uint63.t * (Uint63.t array * Uint63.t array) **)

let centroid comp par sz big t =
  let sb = sz_init comp t (Uint63.of_int (0)) sz big in
  let sb' = sz_acc comp par (sub t (Uint63.of_int (1))) (fst sb) (snd sb) in
  (((fun a i -> Array.unsafe_get a (Uint63.hash i)) comp
     (argmin comp (fst sb') (snd sb') t (Uint63.of_int (0))
       (Uint63.of_int (0)) t)),
  sb')

type lct = { l_st : Uint63.t array; l_m : Uint63.t array; l_b : Uint63.t array }

(** val lkey : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let lkey x lo hi =
  if eqb lo hi
  then add x lo
  else add (add lo (div (sub hi lo) (Uint63.of_int (2)))) (Uint63.of_int (1))

(** val lc_insert :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    lct -> lct **)

let rec lc_insert x s lo hi m b t =
  let k = lkey x lo hi in
  if eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.l_st k) s
  then let cm = (fun a i -> Array.unsafe_get a (Uint63.hash i)) t.l_m k in
       let cb = (fun a i -> Array.unsafe_get a (Uint63.hash i)) t.l_b k in
       let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
       let nb = ltb (add (mul m mid) b) (add (mul cm mid) cb) in
       let wm = if nb then m else cm in
       let wb = if nb then b else cb in
       let om = if nb then cm else m in
       let ob = if nb then cb else b in
       let t1 =
         if nb
         then { l_st = t.l_st; l_m =
                ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.l_m
                  k m);
                l_b =
                ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.l_b
                  k b) }
         else t
       in
       if bdec (ltb lo hi)
       then if ltb (add (mul om lo) ob) (add (mul wm lo) wb)
            then lc_insert x s lo mid om ob t1
            else lc_insert x s (add mid (Uint63.of_int (1))) hi om ob t1
       else t1
  else { l_st =
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.l_st k s);
         l_m =
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.l_m k m);
         l_b =
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.l_b k b) }

(** val lc_query :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> lct ->
    Uint63.t **)

let rec lc_query x s lo hi x0 t =
  let k = lkey x lo hi in
  let v =
    if eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.l_st k) s
    then add
           (mul ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.l_m k) x0)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.l_b k)
    else iNF
  in
  if bdec (ltb lo hi)
  then let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
       let r =
         if leb x0 mid
         then lc_query x s lo mid x0 t
         else lc_query x s (add mid (Uint63.of_int (1))) hi x0 t
       in
       if ltb r v then r else v
  else v

(** val ins_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> lct -> lct **)

let rec ins_loop xp comp d x s t i t0 =
  if bdec (ltb i t)
  then let v = (fun a i -> Array.unsafe_get a (Uint63.hash i)) comp i in
       ins_loop xp comp d x s t (add i (Uint63.of_int (1)))
         (lc_insert x s (Uint63.of_int (0)) (sub x (Uint63.of_int (1)))
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xp
             (sub v (Uint63.of_int (1))))
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d v) t0)
  else t0

(** val qry_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> lct -> Uint63.t array -> Uint63.t
    array **)

let rec qry_loop xp comp d x s t i t0 best =
  if bdec (ltb i t)
  then let u = (fun a i -> Array.unsafe_get a (Uint63.hash i)) comp i in
       let q =
         add ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d u)
           (lc_query x s (Uint63.of_int (0)) (sub x (Uint63.of_int (1)))
             ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xp
               (sub u (Uint63.of_int (1))))
             t0)
       in
       qry_loop xp comp d x s t (add i (Uint63.of_int (1))) t0
         (if ltb q ((fun a i -> Array.unsafe_get a (Uint63.hash i)) best u)
          then (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) best u q
          else best)
  else best

type mst = { m_vis : Uint63.t array; m_comp : Uint63.t array;
             m_par : Uint63.t array; m_d : Uint63.t array;
             m_sz : Uint63.t array; m_big : Uint63.t array; m_T : lct;
             m_best : Uint63.t array }

(** val pick : bool array -> Uint63.t -> Uint63.t -> Uint63.t **)

let pick alive c r =
  if (&&) (ltb c ((fun a -> Uint63.of_int (Array.length a)) alive))
       ((fun a i -> Array.unsafe_get a (Uint63.hash i)) alive c)
  then c
  else r

(** val process :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t -> bool array -> Uint63.t -> Uint63.t -> mst -> Uint63.t * mst **)

let process sa nbr wt xp x alive r rnd s =
  let b1 =
    bfs sa nbr wt alive (mul (Uint63.of_int (2)) rnd) r s.m_vis s.m_comp
      s.m_par s.m_d
  in
  let cr = centroid b1.b_comp b1.b_par s.m_sz s.m_big b1.b_tail in
  let c = pick alive (fst cr) r in
  let b2 =
    bfs sa nbr wt alive
      (add (mul (Uint63.of_int (2)) rnd) (Uint63.of_int (1))) c b1.b_vis
      b1.b_comp b1.b_par b1.b_d
  in
  let t = b2.b_tail in
  let d = relax sa nbr wt alive b2.b_comp t b2 in
  let t0 = ins_loop xp b2.b_comp d x rnd t (Uint63.of_int (0)) s.m_T in
  let best = qry_loop xp b2.b_comp d x rnd t (Uint63.of_int (0)) t0 s.m_best
  in
  (c, { m_vis = b2.b_vis; m_comp = b2.b_comp; m_par = b2.b_par; m_d = d;
  m_sz = (fst (snd cr)); m_big = (snd (snd cr)); m_T = t0; m_best = best })

(** val main_loop :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t -> Uint63.t -> Uint63.t -> bool array -> mst -> Uint63.t array **)

let rec main_loop sa nbr wt xp x r rnd alive s =
  if bdec (ltb r ((fun a -> Uint63.of_int (Array.length a)) alive))
  then if bdec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) alive r)
       then let cS = process sa nbr wt xp x alive r rnd s in
            main_loop sa nbr wt xp x r (add rnd (Uint63.of_int (1)))
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) alive
                (fst cS) false)
              (snd cS)
       else main_loop sa nbr wt xp x (add r (Uint63.of_int (1))) rnd alive s
  else s.m_best

(** val sum_loop :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec sum_loop best n1 i acc =
  if bdec (ltb i n1)
  then sum_loop best n1 (add i (Uint63.of_int (1)))
         (add acc ((fun a i -> Array.unsafe_get a (Uint63.hash i)) best i))
  else acc

(** val yatp_impl :
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t **)

let yatp_impl xp xu xv xw =
  let n = (fun a -> Uint63.of_int (Array.length a)) xp in
  let n1 = add n (Uint63.of_int (1)) in
  let hh =
    add ((fun a -> Uint63.of_int (Array.length a)) xu)
      ((fun a -> Uint63.of_int (Array.length a)) xu)
  in
  let deg =
    deg_loop xu xv hh (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0)))
  in
  let sp =
    start_loop deg n1 (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) (add n1 (Uint63.of_int (1)))
        (Uint63.of_int (0)))
      ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0)))
  in
  let nw =
    fill_loop xu xv xw hh (Uint63.of_int (0)) (snd sp)
      ((fun n d -> Array.make (Uint63.hash n) d) hh (Uint63.of_int (0)))
      ((fun n d -> Array.make (Uint63.hash n) d) hh (Uint63.of_int (0)))
  in
  let x =
    add (max_loop xp n (Uint63.of_int (0)) (Uint63.of_int (0)))
      (Uint63.of_int (1))
  in
  let alive =
    true_loop n1 (Uint63.of_int (1))
      ((fun n d -> Array.make (Uint63.hash n) d) n1 false)
  in
  let s = { m_vis =
    ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0)));
    m_comp =
    ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0)));
    m_par =
    ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0))); m_d =
    ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0)));
    m_sz =
    ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0)));
    m_big =
    ((fun n d -> Array.make (Uint63.hash n) d) n1 (Uint63.of_int (0))); m_T =
    { l_st =
    ((fun n d -> Array.make (Uint63.hash n) d) (add x x) (Uint63.of_int (0)));
    l_m =
    ((fun n d -> Array.make (Uint63.hash n) d) (add x x) (Uint63.of_int (0)));
    l_b =
    ((fun n d -> Array.make (Uint63.hash n) d) (add x x) (Uint63.of_int (0))) };
    m_best = ((fun n d -> Array.make (Uint63.hash n) d) n1 iNF) }
  in
  let best =
    main_loop (fst sp) (fst nw) (snd nw) xp x (Uint63.of_int (1))
      (Uint63.of_int (1)) alive s
  in
  sum_loop best n1 (Uint63.of_int (1)) (Uint63.of_int (0))

(** val yatp :
    uint array -> uint array -> uint array -> uint array -> uint **)

let yatp =
  yatp_impl
