
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

(** val nil : Uint63.t **)

let nil =
  (Uint63.of_int (-1))

type fh = { hkey : Uint63.t Marray.t; hpar : Uint63.t Marray.t;
            hchd : Uint63.t Marray.t; hlft : Uint63.t Marray.t;
            hrgt : Uint63.t Marray.t; hdeg : Uint63.t Marray.t;
            hmrk : Uint63.t Marray.t; hbuf : Uint63.t Marray.t;
            hmin : Uint63.t }

(** val s_key : fh -> Uint63.t -> Uint63.t -> fh **)

let s_key h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = (set key i v); hpar = par; hchd = chd; hlft = lft; hrgt = rgt;
  hdeg = deg; hmrk = mrk; hbuf = buf; hmin = mn }

(** val s_par : fh -> Uint63.t -> Uint63.t -> fh **)

let s_par h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = key; hpar = (set par i v); hchd = chd; hlft = lft; hrgt = rgt;
  hdeg = deg; hmrk = mrk; hbuf = buf; hmin = mn }

(** val s_chd : fh -> Uint63.t -> Uint63.t -> fh **)

let s_chd h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = key; hpar = par; hchd = (set chd i v); hlft = lft; hrgt = rgt;
  hdeg = deg; hmrk = mrk; hbuf = buf; hmin = mn }

(** val s_lft : fh -> Uint63.t -> Uint63.t -> fh **)

let s_lft h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = key; hpar = par; hchd = chd; hlft = (set lft i v); hrgt = rgt;
  hdeg = deg; hmrk = mrk; hbuf = buf; hmin = mn }

(** val s_rgt : fh -> Uint63.t -> Uint63.t -> fh **)

let s_rgt h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = (set rgt i v);
  hdeg = deg; hmrk = mrk; hbuf = buf; hmin = mn }

(** val s_deg : fh -> Uint63.t -> Uint63.t -> fh **)

let s_deg h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
  (set deg i v); hmrk = mrk; hbuf = buf; hmin = mn }

(** val s_mrk : fh -> Uint63.t -> Uint63.t -> fh **)

let s_mrk h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg = deg;
  hmrk = (set mrk i v); hbuf = buf; hmin = mn }

(** val s_buf : fh -> Uint63.t -> Uint63.t -> fh **)

let s_buf h i v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = mn } = h
  in
  { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg = deg;
  hmrk = mrk; hbuf = (set buf i v); hmin = mn }

(** val s_min : fh -> Uint63.t -> fh **)

let s_min h v =
  let { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg =
    deg; hmrk = mrk; hbuf = buf; hmin = _ } = h
  in
  { hkey = key; hpar = par; hchd = chd; hlft = lft; hrgt = rgt; hdeg = deg;
  hmrk = mrk; hbuf = buf; hmin = v }

(** val ring_ins : fh -> Uint63.t -> Uint63.t -> fh **)

let ring_ins h a x =
  let b = get h.hrgt a in s_lft (s_rgt (s_lft (s_rgt h a x) x a) x b) b x

(** val root_add : fh -> Uint63.t -> fh **)

let root_add h x =
  let m = h.hmin in
  if eqb m nil
  then s_min (s_rgt (s_lft h x x) x x) x
  else let h1 = ring_ins h m x in
       if ltb (get h1.hkey x) (get h1.hkey m) then s_min h1 x else h1

(** val fh_insert : fh -> Uint63.t -> Uint63.t -> fh **)

let fh_insert h x k =
  root_add
    (s_mrk
      (s_deg (s_chd (s_par (s_key h x k) x nil) x nil) x (Uint63.of_int (0)))
      x (Uint63.of_int (0)))
    x

(** val fh_cut : fh -> Uint63.t -> Uint63.t -> fh **)

let fh_cut h x y =
  let h1 =
    if eqb (get h.hdeg y) (Uint63.of_int (1))
    then s_chd h y nil
    else let a = get h.hlft x in
         let b = get h.hrgt x in
         let h' = s_lft (s_rgt h a b) b a in
         if eqb (get h'.hchd y) x then s_chd h' y b else h'
  in
  let h2 = s_deg h1 y (sub (get h1.hdeg y) (Uint63.of_int (1))) in
  root_add (s_mrk (s_par h2 x nil) x (Uint63.of_int (0))) x

(** val ccut : fh -> Uint63.t -> Uint63.t -> fh **)

let rec ccut h y cnt =
  if bdec (ltb (Uint63.of_int (0)) cnt)
  then let z = get h.hpar y in
       if eqb z nil
       then h
       else if eqb (get h.hmrk y) (Uint63.of_int (0))
            then s_mrk h y (Uint63.of_int (1))
            else ccut (fh_cut h y z) z (sub cnt (Uint63.of_int (1)))
  else h

(** val fh_decrease : fh -> Uint63.t -> Uint63.t -> fh **)

let fh_decrease h x k =
  let h1 = s_key h x k in
  let y = get h1.hpar x in
  let h2 =
    if eqb y nil
    then h1
    else if ltb k (get h1.hkey y)
         then let n = length h1.hpar in ccut (fh_cut h1 x y) y n
         else h1
  in
  if ltb k (get h2.hkey h2.hmin) then s_min h2 x else h2

(** val fh_link : fh -> Uint63.t -> Uint63.t -> fh **)

let fh_link h y x =
  let h1 =
    if eqb (get h.hdeg x) (Uint63.of_int (0))
    then s_rgt (s_lft (s_chd h x y) y y) y y
    else ring_ins h (get h.hchd x) y
  in
  s_mrk (s_deg (s_par h1 y x) x (add (get h1.hdeg x) (Uint63.of_int (1)))) y
    (Uint63.of_int (0))

(** val link_loop :
    fh -> Uint63.t -> Uint63.t -> Uint63.t -> fh * Uint63.t **)

let rec link_loop h x d n =
  if bdec (ltb d n)
  then let y = get h.hbuf d in
       if eqb y nil
       then ((s_buf h d x), d)
       else let h1 = s_buf h d nil in
            if ltb (get h1.hkey y) (get h1.hkey x)
            then link_loop (fh_link h1 x y) y (add d (Uint63.of_int (1))) n
            else link_loop (fh_link h1 y x) x (add d (Uint63.of_int (1))) n
  else (h, d)

(** val proc : fh -> Uint63.t -> Uint63.t -> fh * Uint63.t **)

let proc h w md =
  let h1 = s_par h w nil in
  let n = length h1.hbuf in
  let r = link_loop h1 w (get h1.hdeg w) n in
  ((fst r), (if ltb md (snd r) then snd r else md))

(** val walk :
    fh -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> fh * Uint63.t **)

let rec walk h cur stop md cnt =
  if eqb cur stop
  then (h, md)
  else if bdec (ltb (Uint63.of_int (0)) cnt)
       then let nx = get h.hrgt cur in
            let r = proc h cur md in
            walk (fst r) nx stop (snd r) (sub cnt (Uint63.of_int (1)))
       else (h, md)

(** val rebuild : fh -> Uint63.t -> Uint63.t -> fh **)

let rec rebuild h d m =
  if bdec (ltb d m)
  then let x = get h.hbuf d in
       let h1 = if eqb x nil then h else root_add (s_buf h d nil) x in
       rebuild h1 (add d (Uint63.of_int (1))) m
  else h

(** val fh_extract : fh -> fh * Uint63.t **)

let fh_extract h =
  let z = h.hmin in
  let c = get h.hchd z in
  let dz = get h.hdeg z in
  let n = length h.hbuf in
  let h0 = s_min h nil in
  let r1 = walk h0 (get h0.hrgt z) z (Uint63.of_int (0)) n in
  let r2 =
    if eqb dz (Uint63.of_int (0))
    then r1
    else let nx = get (fst r1).hrgt c in
         let r = proc (fst r1) c (snd r1) in walk (fst r) nx c (snd r) n
  in
  let m = add (snd r2) (Uint63.of_int (1)) in
  ((rebuild (fst r2) (Uint63.of_int (0)) m), z)

(** val build :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec build u v head nxt j m =
  if bdec (ltb j m)
  then let a = get u j in
       let b = get v j in
       let e1 = add (mul (Uint63.of_int (2)) j) (Uint63.of_int (1)) in
       let e2 = add (mul (Uint63.of_int (2)) j) (Uint63.of_int (2)) in
       let nxt1 = set nxt e1 (get head a) in
       let head1 = set head a e1 in
       let nxt2 = set nxt1 e2 (get head1 b) in
       let head2 = set head1 b e2 in
       build u v head2 nxt2 (add j (Uint63.of_int (1))) m
  else (head, nxt)

(** val relax :
    fh -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> fh * Uint63.t Marray.t **)

let relax h st v nk =
  let s = get st v in
  if eqb s (Uint63.of_int (0))
  then ((fh_insert h v nk), (set st v (Uint63.of_int (1))))
  else if eqb s (Uint63.of_int (1))
       then if ltb nk (get h.hkey v)
            then ((fh_decrease h v nk), st)
            else (h, st)
       else (h, st)

(** val edges :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> (fh * Uint63.t Marray.t)
    -> Uint63.t -> fh * Uint63.t Marray.t **)

let rec edges u v dl nxt c f kz hs e =
  if eqb e (Uint63.of_int (0))
  then hs
  else let j = div (sub e (Uint63.of_int (1))) (Uint63.of_int (2)) in
       let y =
         if eqb (mod0 (sub e (Uint63.of_int (1))) (Uint63.of_int (2)))
              (Uint63.of_int (0))
         then get v j
         else get u j
       in
       let l = get dl j in
       let hs1 =
         if leb l f
         then relax (fst hs) (snd hs) (add (mul y c) (sub f l)) kz
         else hs
       in
       let e' = get nxt e in
       if bdec (ltb e' e) then edges u v dl nxt c f kz hs1 e' else hs1

(** val expand :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> (fh * Uint63.t Marray.t) -> Uint63.t -> fh * Uint63.t Marray.t **)

let expand p u v dl head nxt c cap hs z =
  let x = div z c in
  let f = mod0 z c in
  let kz = get (fst hs).hkey z in
  let hs1 =
    if ltb f cap
    then relax (fst hs) (snd hs) (add z (Uint63.of_int (1)))
           (add kz (get p x))
    else hs
  in
  edges u v dl nxt c f kz hs1 (get head x)

(** val dijk :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> (fh * Uint63.t Marray.t) -> Uint63.t -> Uint63.t
    option **)

let rec dijk p u v dl head nxt c cap g hs cnt =
  if eqb (fst hs).hmin nil
  then None
  else if bdec (ltb (Uint63.of_int (0)) cnt)
       then let r = fh_extract (fst hs) in
            let z = snd r in
            let st1 = set (snd hs) z (Uint63.of_int (2)) in
            if eqb (div z c) g
            then Some (get (fst r).hkey z)
            else dijk p u v dl head nxt c cap g
                   (expand p u v dl head nxt c cap ((fst r), st1) z)
                   (sub cnt (Uint63.of_int (1)))
       else None

(** val query :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t option **)

let query n p u v dl head nxt cap s g =
  let c = add cap (Uint63.of_int (1)) in
  let n0 = mul n c in
  let h0 = { hkey = (make n0 (Uint63.of_int (0))); hpar = (make n0 nil);
    hchd = (make n0 nil); hlft = (make n0 nil); hrgt = (make n0 nil); hdeg =
    (make n0 (Uint63.of_int (0))); hmrk = (make n0 (Uint63.of_int (0)));
    hbuf = (make n0 nil); hmin = nil }
  in
  let src = mul s c in
  dijk p u v dl head nxt c cap g ((fh_insert h0 src (Uint63.of_int (0))),
    (set (make n0 (Uint63.of_int (0))) src (Uint63.of_int (1)))) n0

(** val qloop :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    option Marray.t -> Uint63.t -> Uint63.t -> Uint63.t option Marray.t **)

let rec qloop n p u v dl head nxt cs ss es out i q =
  if bdec (ltb i q)
  then qloop n p u v dl head nxt cs ss es
         (set out i
           (query n p u v dl head nxt (get cs i) (get ss i) (get es i)))
         (add i (Uint63.of_int (1))) q
  else out

(** val fulltank_impl :
    uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t
    -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint option Marray.t **)

let fulltank_impl n p u v d c s e =
  let m = length u in
  let hn =
    build u v (make n (Uint63.of_int (0)))
      (make (add (mul (Uint63.of_int (2)) m) (Uint63.of_int (1)))
        (Uint63.of_int (0)))
      (Uint63.of_int (0)) m
  in
  let q = length c in
  qloop n p u v d (fst hn) (snd hn) c s e (make q None) (Uint63.of_int (0)) q

(** val fulltank :
    uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t
    -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint option Marray.t **)

let fulltank =
  fulltank_impl
