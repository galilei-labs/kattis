
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

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

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

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

(** val gcd_loop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec gcd_loop a b =
  if bdec (eqb b (Uint63.of_int (0))) then a else gcd_loop b (mod0 a b)

(** val igcd : Uint63.t -> Uint63.t -> Uint63.t **)

let igcd =
  gcd_loop

(** val capf : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let capf x i j =
  if eqb i j
  then (Uint63.of_int (0))
  else let g = igcd (get x i) (get x j) in
       if ltb (Uint63.of_int (1)) g then g else (Uint63.of_int (0))

(** val fill_row :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec fill_row x n i tbl j =
  if bdec (ltb j n)
  then let c = capf x i j in
       fill_row x n i (set (set tbl (add (mul i n) j) c) (add (mul j n) i) c)
         (add j (Uint63.of_int (1)))
  else tbl

(** val fill_tab :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec fill_tab x n tbl i =
  if bdec (ltb i n)
  then fill_tab x n (fill_row x n i tbl i) (add i (Uint63.of_int (1)))
  else tbl

(** val amin :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec amin x n i best =
  if bdec (ltb i n)
  then amin x n (add i (Uint63.of_int (1)))
         (if ltb (get x i) (get x best) then i else best)
  else best

(** val amax :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec amax x n i best =
  if bdec (ltb i n)
  then amax x n (add i (Uint63.of_int (1)))
         (if ltb (get x best) (get x i) then i else best)
  else best

(** val rng_ok : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool **)

let rec rng_ok x n i =
  if bdec (ltb i n)
  then if (&&) (leb (Uint63.of_int (2)) (get x i))
            (leb (get x i) (Uint63.of_int (2000000000)))
       then rng_ok x n (add i (Uint63.of_int (1)))
       else false
  else true

(** val sat :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> ((Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t **)

let rec sat n s t tbl ex q ql v =
  if bdec (ltb v n)
  then let c = get tbl (add (mul s n) v) in
       let tbl1 = set tbl (add (mul s n) v) (Uint63.of_int (0)) in
       let tbl2 =
         set tbl1 (add (mul v n) s) (add (get tbl1 (add (mul v n) s)) c)
       in
       let ex1 = set ex v c in
       let b =
         (&&) ((&&) (ltb (Uint63.of_int (0)) c) (negb (eqb v t)))
           (negb (eqb v s))
       in
       let q1 = if b then set q ql v else q in
       let ql1 = if b then add ql (Uint63.of_int (1)) else ql in
       sat n s t tbl2 ex1 q1 ql1 (add v (Uint63.of_int (1)))
  else (((tbl, ex), q), ql)

(** val amap :
    (Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec amap f a i m =
  if bdec (ltb i m)
  then let o = get a i in
       let w = f i o in
       amap f (if eqb w o then a else set a i w) (add i (Uint63.of_int (1))) m
  else a

(** val relaxF :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let relaxF tbl n b l1 a o =
  if (&&) (ltb (Uint63.of_int (0)) (get tbl (add (mul a n) b))) (ltb l1 o)
  then l1
  else o

(** val has_val :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let rec has_val d n l j =
  if bdec (ltb j n)
  then if eqb (get d j) l
       then true
       else has_val d n l (add j (Uint63.of_int (1)))
  else false

(** val lscan :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec lscan tbl n l d j =
  if bdec (ltb j n)
  then lscan tbl n l
         (if eqb (get d j) l
          then amap (relaxF tbl n j (add l (Uint63.of_int (1)))) d
                 (Uint63.of_int (0)) n
          else d)
         (add j (Uint63.of_int (1)))
  else d

(** val layers :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec layers tbl n l d =
  if bdec (ltb l n)
  then if has_val d n l (Uint63.of_int (0))
       then layers tbl n (add l (Uint63.of_int (1)))
              (lscan tbl n l d (Uint63.of_int (0)))
       else d
  else d

(** val bfs :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let bfs tbl n t =
  layers tbl n (Uint63.of_int (0)) (set (make n n) t (Uint63.of_int (0)))

(** val maxF : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let maxF d y o =
  if ltb o (get d y) then get d y else o

(** val glob :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let glob tbl n t h =
  let d = bfs tbl n t in amap (maxF d) h (Uint63.of_int (0)) n

(** val cntl :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec cntl h cnt n i =
  if bdec (ltb i n)
  then let k = get h i in
       cntl h (set cnt k (add (get cnt k) (Uint63.of_int (1)))) n
         (add i (Uint63.of_int (1)))
  else cnt

(** val count : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let count h n =
  cntl h (make (add n (Uint63.of_int (1))) (Uint63.of_int (0))) n
    (Uint63.of_int (0))

(** val rmin :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t -> Uint63.t **)

let rec rmin tbl n u h b acc =
  if bdec (ltb b n)
  then rmin tbl n u h (add b (Uint63.of_int (1)))
         (if (&&) (ltb (Uint63.of_int (0)) (get tbl (add (mul u n) b)))
               (ltb (add (get h b) (Uint63.of_int (1))) acc)
          then add (get h b) (Uint63.of_int (1))
          else acc)
  else acc

(** val no_height :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let rec no_height h n k i =
  if bdec (ltb i n)
  then if eqb (get h i) k
       then false
       else no_height h n k (add i (Uint63.of_int (1)))
  else true

(** val liftF : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let liftF n k _ o =
  if (&&) (ltb k o) (ltb o n) then n else o

(** val lift :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let lift h n k =
  amap (liftF n k) h (Uint63.of_int (0)) n

(** val cnt_lift :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec cnt_lift h cnt n k i =
  if bdec (ltb i n)
  then let o = get h i in
       cnt_lift h
         (if (&&) (ltb k o) (ltb o n)
          then set cnt o (sub (get cnt o) (Uint63.of_int (1)))
          else cnt)
         n k (add i (Uint63.of_int (1)))
  else cnt

(** val active :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let active ex h n s t v =
  (&&)
    ((&&) ((&&) (ltb (Uint63.of_int (0)) (get ex v)) (ltb (get h v) n))
      (negb (eqb v s)))
    (negb (eqb v t))

(** val find_act :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t **)

let rec find_act ex h n s t i =
  if bdec (ltb i n)
  then if active ex h n s t i
       then i
       else find_act ex h n s t (add i (Uint63.of_int (1)))
  else n

(** val adm :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> bool **)

let adm tbl h n u v =
  (&&) (ltb (Uint63.of_int (0)) (get tbl (add (mul u n) v)))
    (eqb (get h u) (add (get h v) (Uint63.of_int (1))))

(** val enq_pos : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let enq_pos qh ql n =
  let p = add qh ql in if ltb p n then p else sub p n

type st = { s_tbl : Uint63.t Marray.t; s_ex : Uint63.t Marray.t;
            s_h : Uint63.t Marray.t; s_cur : Uint63.t Marray.t;
            s_cnt : Uint63.t Marray.t; s_q : Uint63.t Marray.t;
            s_qh : Uint63.t; s_ql : Uint63.t; s_cu : Uint63.t; s_rl : 
            Uint63.t }

(** val mloop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec mloop n s t tbl ex h cur cnt q qh ql cu rl =
  if bdec (ltb cu n)
  then let v = get cur cu in
       if bdec (ltb v n)
       then if bdec (adm tbl h n cu v)
            then let r = get tbl (add (mul cu n) v) in
                 let e = get ex cu in
                 let d = if ltb e r then e else r in
                 let tbl1 = set tbl (add (mul cu n) v) (sub r d) in
                 let tbl2 =
                   set tbl1 (add (mul v n) cu)
                     (add (get tbl1 (add (mul v n) cu)) d)
                 in
                 let ev = get ex v in
                 let ex1 = set ex cu (sub e d) in
                 let ex2 = set ex1 v (add ev d) in
                 let b =
                   (&&)
                     ((&&)
                       ((&&) (eqb ev (Uint63.of_int (0))) (negb (eqb v t)))
                       (negb (eqb v s)))
                     (ltb ql n)
                 in
                 let q1 = if b then set q (enq_pos qh ql n) v else q in
                 let ql1 = if b then add ql (Uint63.of_int (1)) else ql in
                 let cu1 = if eqb (sub e d) (Uint63.of_int (0)) then n else cu
                 in
                 mloop n s t tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl
            else mloop n s t tbl ex h
                   (set cur cu (add v (Uint63.of_int (1)))) cnt q qh ql cu rl
       else let oh = get h cu in
            let nh = rmin tbl n cu h (Uint63.of_int (0)) n in
            let h1 = set h cu nh in
            let cur1 = set cur cu (Uint63.of_int (0)) in
            let co = sub (get cnt oh) (Uint63.of_int (1)) in
            let cnt1 = set cnt oh co in
            let cnt2 = set cnt1 nh (add (get cnt1 nh) (Uint63.of_int (1))) in
            let g =
              (&&)
                ((&&)
                  ((&&) (eqb co (Uint63.of_int (0)))
                    (ltb (Uint63.of_int (0)) oh))
                  (ltb oh n))
                (no_height h1 n oh (Uint63.of_int (0)))
            in
            let cnt3 =
              if g then cnt_lift h1 cnt2 n oh (Uint63.of_int (0)) else cnt2
            in
            let h2 = if g then lift h1 n oh else h1 in
            let rl1 = add rl (Uint63.of_int (1)) in
            let gl = leb n rl1 in
            let h3 = if gl then glob tbl n t h2 else h2 in
            let cur2 = if gl then make n (Uint63.of_int (0)) else cur1 in
            let cnt4 = if gl then count h3 n else cnt3 in
            let rl2 = if gl then (Uint63.of_int (0)) else rl1 in
            let cu1 = if ltb (get h3 cu) n then cu else n in
            mloop n s t tbl ex h3 cur2 cnt4 q qh ql cu1 rl2
  else if bdec (ltb (Uint63.of_int (0)) ql)
       then let v = get q qh in
            let qh1 =
              if eqb (add qh (Uint63.of_int (1))) n
              then (Uint63.of_int (0))
              else add qh (Uint63.of_int (1))
            in
            let cu1 = if (&&) (ltb v n) (active ex h n s t v) then v else n in
            mloop n s t tbl ex h cur cnt q qh1 (sub ql (Uint63.of_int (1)))
              cu1 rl
       else let v = find_act ex h n s t (Uint63.of_int (0)) in
            if bdec (ltb v n)
            then mloop n s t tbl ex h cur cnt q qh ql v rl
            else get ex t

(** val nn : Uint63.t Marray.t -> Uint63.t **)

let nn =
  length

(** val ss : Uint63.t Marray.t -> Uint63.t **)

let ss x =
  amin x (nn x) (Uint63.of_int (1)) (Uint63.of_int (0))

(** val tt : Uint63.t Marray.t -> Uint63.t **)

let tt x =
  amax x (nn x) (Uint63.of_int (1)) (Uint63.of_int (0))

(** val guard : Uint63.t Marray.t -> bool **)

let guard x =
  (&&)
    ((&&)
      ((&&) (leb (Uint63.of_int (2)) (nn x))
        (leb (nn x) (Uint63.of_int (1000))))
      (rng_ok x (nn x) (Uint63.of_int (0))))
    (negb (eqb (ss x) (tt x)))

(** val init_state : Uint63.t Marray.t -> st **)

let init_state x =
  let n = nn x in
  let s = ss x in
  let t = tt x in
  let tbl0 =
    fill_tab x n (make (mul n n) (Uint63.of_int (0))) (Uint63.of_int (0))
  in
  let p =
    sat n s t tbl0 (make n (Uint63.of_int (0))) (make n (Uint63.of_int (0)))
      (Uint63.of_int (0)) (Uint63.of_int (0))
  in
  let h0 = set (make n (Uint63.of_int (0))) s n in
  let h1 = glob (fst (fst (fst p))) n t h0 in
  { s_tbl = (fst (fst (fst p))); s_ex = (snd (fst (fst p))); s_h = h1;
  s_cur = (make n (Uint63.of_int (0))); s_cnt = (count h1 n); s_q =
  (snd (fst p)); s_qh = (Uint63.of_int (0)); s_ql = (snd p); s_cu = n; s_rl =
  (Uint63.of_int (0)) }

(** val mazemovement_impl : uint Marray.t -> uint **)

let mazemovement_impl x =
  if bdec (guard x)
  then let s = init_state x in
       mloop (nn x) (ss x) (tt x) s.s_tbl s.s_ex s.s_h s.s_cur s.s_cnt s.s_q
         s.s_qh s.s_ql s.s_cu s.s_rl
  else (Uint63.of_int (0))

(** val mazemovement : uint Marray.t -> uint **)

let mazemovement =
  mazemovement_impl
