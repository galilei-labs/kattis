
type comparison =
| Eq
| Lt
| Gt

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

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

type char63 = Uint63.t

type string = Pstring.t

(** val length0 : string -> Uint63.t **)

let length0 = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

(** val compare : string -> string -> comparison **)

let compare = (fun x y -> let c = Pstring.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val hloop :
    string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec hloop x p len j h =
  if bdec (ltb j len)
  then hloop x p len (add j (Uint63.of_int (1)))
         (add (mul h (Uint63.of_int (31)))
           (if eqb j p
            then (Uint63.of_int (1))
            else add (get0 x j) (Uint63.of_int (2))))
  else h

(** val khash : Uint63.t -> string -> Uint63.t -> Uint63.t **)

let khash m x p =
  let len = length0 x in
  mod0 (hloop x p len (Uint63.of_int (0)) (Uint63.of_int (7))) m

(** val kloop :
    string -> string -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let rec kloop x y p len j =
  if bdec (ltb j len)
  then if (||) (eqb j p) (eqb (get0 x j) (get0 y j))
       then kloop x y p len (add j (Uint63.of_int (1)))
       else false
  else true

(** val keq : string -> string -> Uint63.t -> bool **)

let keq x y p =
  let len = length0 x in
  if eqb len (length0 y) then kloop x y p len (Uint63.of_int (0)) else false

(** val find :
    Uint63.t Marray.t -> (Uint63.t -> bool) -> Uint63.t -> Uint63.t **)

let rec find nx test ptr =
  if eqb ptr (Uint63.of_int (0))
  then (Uint63.of_int (0))
  else if test (sub ptr (Uint63.of_int (1)))
       then ptr
       else if bdec (ltb (get nx (sub ptr (Uint63.of_int (1)))) ptr)
            then find nx test (get nx (sub ptr (Uint63.of_int (1))))
            else (Uint63.of_int (0))

(** val m_key : Uint63.t **)

let m_key =
  (Uint63.of_int (1048576))

(** val m_word : Uint63.t **)

let m_word =
  (Uint63.of_int (65536))

(** val wbuild :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t Marray.t **)

let rec wbuild xd n i wl wb wn =
  if bdec (ltb i n)
  then let w = get xd i in
       let h = khash m_word w (length0 w) in
       let old = get wb h in
       wbuild xd n (add i (Uint63.of_int (1))) (set wl i (length0 w))
         (set wb h (add i (Uint63.of_int (1)))) (set wn i old)
  else ((wl, wb), wn)

(** val wtest : string Marray.t -> string -> Uint63.t -> bool **)

let wtest xd q y =
  match compare (get xd y) q with
  | Eq -> true
  | _ -> false

(** val lookup :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> string ->
    Uint63.t **)

let lookup xd wb wn q =
  let h = khash m_word q (length0 q) in
  let ptr = get wb h in find wn (wtest xd q) ptr

(** val ktest : string Marray.t -> string -> Uint63.t -> Uint63.t -> bool **)

let ktest xd w p y =
  (&&) (eqb (mod0 y (Uint63.of_int (16))) p)
    (keq (get xd (lsr0 y (Uint63.of_int (4)))) w p)

(** val build :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t **)

let rec build xd n16 e cls bk bn hd cn =
  if bdec (ltb e n16)
  then let w = get xd (lsr0 e (Uint63.of_int (4))) in
       let p = mod0 e (Uint63.of_int (16)) in
       if ltb p (length0 w)
       then let h = khash m_key w p in
            let old = get bk h in
            let r = find bn (ktest xd w p) old in
            let c =
              if eqb r (Uint63.of_int (0))
              then e
              else get cls (sub r (Uint63.of_int (1)))
            in
            let oldc = get hd c in
            build xd n16 (add e (Uint63.of_int (1))) (set cls e c)
              (set bk h (add e (Uint63.of_int (1)))) (set bn e old)
              (set hd c (add e (Uint63.of_int (1)))) (set cn e oldc)
       else build xd n16 (add e (Uint63.of_int (1))) cls bk bn hd cn
  else ((cls, hd), cn)

(** val mkb :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t Marray.t -> (((Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t Marray.t **)

let mkb d p q t m =
  ((((d, p), q), t), m)

(** val sD :
    ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t **)

let sD = function
| (p, _) -> let (p0, _) = p in let (p1, _) = p0 in let (d, _) = p1 in d

(** val sP :
    ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t **)

let sP = function
| (p, _) -> let (p0, _) = p in let (p1, _) = p0 in let (_, p2) = p1 in p2

(** val sQ :
    ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t **)

let sQ = function
| (p, _) -> let (p0, _) = p in let (_, q) = p0 in q

(** val sT :
    ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t **)

let sT = function
| (p, _) -> let (_, t) = p in t

(** val sM :
    ((((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t) -> Uint63.t Marray.t **)

let sM = function
| (_, m) -> m

(** val cwalk :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((((Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t
    Marray.t) -> (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t **)

let rec cwalk cn u du ptr s =
  if eqb ptr (Uint63.of_int (0))
  then s
  else let e = sub ptr (Uint63.of_int (1)) in
       let v = lsr0 e (Uint63.of_int (4)) in
       let s' =
         if eqb (get (sD s) v) (Uint63.of_int (0))
         then mkb (set (sD s) v (add du (Uint63.of_int (1))))
                (set (sP s) v u) (set (sQ s) (sT s) v)
                (add (sT s) (Uint63.of_int (1))) (sM s)
         else s
       in
       if bdec (ltb (get cn e) ptr) then cwalk cn u du (get cn e) s' else s'

(** val ploop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((((Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t
    Marray.t) -> (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t **)

let rec ploop cls hd cn u du base len p s =
  if bdec (ltb p len)
  then let c = get cls (add base p) in
       if eqb (get (sM s) c) (Uint63.of_int (0))
       then let s1 = cwalk cn u du (get hd c) s in
            ploop cls hd cn u du base len (add p (Uint63.of_int (1)))
              (mkb (sD s1) (sP s1) (sQ s1) (sT s1)
                (set (sM s1) c (Uint63.of_int (1))))
       else ploop cls hd cn u du base len (add p (Uint63.of_int (1))) s
  else s

(** val bfs :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> ((((Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t Marray.t) ->
    (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t) * Uint63.t Marray.t **)

let rec bfs cls hd cn wl n qh s =
  if bdec (ltb qh n)
  then if ltb qh (sT s)
       then let u = get (sQ s) qh in
            let len = get wl u in
            let s' =
              ploop cls hd cn u (get (sD s) u) (mul u (Uint63.of_int (16)))
                len (Uint63.of_int (0)) s
            in
            bfs cls hd cn wl n (add qh (Uint63.of_int (1))) s'
       else s
  else s

(** val bfs_from :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> (((Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t) * Uint63.t
    Marray.t **)

let bfs_from cls hd cn wl n n16 s0 =
  bfs cls hd cn wl n (Uint63.of_int (0))
    (mkb (set (make n (Uint63.of_int (0))) s0 (Uint63.of_int (1)))
      (make n (Uint63.of_int (0)))
      (set (make n (Uint63.of_int (0))) (Uint63.of_int (0)) s0)
      (Uint63.of_int (1)) (make n16 (Uint63.of_int (0))))

(** val recon :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    string Marray.t -> string Marray.t **)

let rec recon xd d p v out =
  let out' = set out (sub (get d v) (Uint63.of_int (1))) (get xd v) in
  if leb (get d v) (Uint63.of_int (1))
  then out'
  else if bdec (ltb (get d (get p v)) (get d v))
       then recon xd d p (get p v) out'
       else out'

(** val answer2 :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> string -> string Marray.t option **)

let answer2 xd n n16 cls hd cn wl wb wn s0 tgt =
  let rt = lookup xd wb wn tgt in
  if eqb rt (Uint63.of_int (0))
  then None
  else let t = sub rt (Uint63.of_int (1)) in
       let st = bfs_from cls hd cn wl n n16 s0 in
       let dt = get (sD st) t in
       if eqb dt (Uint63.of_int (0))
       then None
       else Some (recon xd (sD st) (sP st) t (make dt (get xd t)))

(** val answer1 :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> string -> string -> string Marray.t option **)

let answer1 xd n n16 cls hd cn wl wb wn src tgt =
  let rs = lookup xd wb wn src in
  if eqb rs (Uint63.of_int (0))
  then None
  else let s0 = sub rs (Uint63.of_int (1)) in
       (match compare src tgt with
        | Eq -> Some (make (Uint63.of_int (1)) (get xd s0))
        | _ -> answer2 xd n n16 cls hd cn wl wb wn s0 tgt)

(** val qloop :
    string Marray.t -> string Marray.t -> string Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t -> string Marray.t option Marray.t -> string
    Marray.t option Marray.t **)

let rec qloop xd xs xt n n16 cls hd cn wl wb wn nq q out =
  if bdec (ltb q nq)
  then qloop xd xs xt n n16 cls hd cn wl wb wn nq (add q (Uint63.of_int (1)))
         (set out q
           (answer1 xd n n16 cls hd cn wl wb wn (get xs q) (get xt q)))
  else out

(** val doublets_impl :
    string Marray.t -> string Marray.t -> string Marray.t -> string Marray.t
    option Marray.t **)

let doublets_impl xd xs xt =
  let n = length xd in
  let n16 = mul n (Uint63.of_int (16)) in
  let (p, wn) =
    wbuild xd n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (make m_word (Uint63.of_int (0))) (make n (Uint63.of_int (0)))
  in
  let (wl, wb) = p in
  let (p0, cn) =
    build xd n16 (Uint63.of_int (0)) (make n16 (Uint63.of_int (0)))
      (make m_key (Uint63.of_int (0))) (make n16 (Uint63.of_int (0)))
      (make n16 (Uint63.of_int (0))) (make n16 (Uint63.of_int (0)))
  in
  let (cls, hd) = p0 in
  let nq = length xs in
  qloop xd xs xt n n16 cls hd cn wl wb wn nq (Uint63.of_int (0))
    (make nq None)

module DoubletsImpl =
 struct
  (** val doublets :
      string Marray.t -> string Marray.t -> string Marray.t -> string
      Marray.t option Marray.t **)

  let doublets =
    doublets_impl
 end
