
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type comparison =
| Eq
| Lt
| Gt

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

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

(** val make0 : Uint63.t -> char63 -> string **)

let make0 = Pstring.make

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

(** val splitc : Uint63.t -> Uint63.t -> bool **)

let splitc lo hi =
  (&&) (ltb lo hi) (ltb (Uint63.of_int (1)) (sub hi lo))

(** val midp : Uint63.t -> Uint63.t -> Uint63.t **)

let midp lo hi =
  add lo (div (sub hi lo) (Uint63.of_int (2)))

(** val init_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec init_loop a n k =
  if bdec (ltb k n)
  then init_loop (set a k k) n (add k (Uint63.of_int (1)))
  else a

(** val cmpw : string Marray.t -> Uint63.t -> Uint63.t -> bool **)

let cmpw x i j =
  match compare (get x i) (get x j) with
  | Gt -> false
  | _ -> true

(** val merge_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec merge_loop x src dst iend jend i j k =
  if bdec (ltb i iend)
  then if bdec (ltb j jend)
       then if cmpw x (get src i) (get src j)
            then merge_loop x src (set dst k (get src i)) iend jend
                   (add i (Uint63.of_int (1))) j (add k (Uint63.of_int (1)))
            else merge_loop x src (set dst k (get src j)) iend jend i
                   (add j (Uint63.of_int (1))) (add k (Uint63.of_int (1)))
       else merge_loop x src (set dst k (get src i)) iend jend
              (add i (Uint63.of_int (1))) j (add k (Uint63.of_int (1)))
  else if bdec (ltb j jend)
       then merge_loop x src (set dst k (get src j)) iend jend i
              (add j (Uint63.of_int (1))) (add k (Uint63.of_int (1)))
       else dst

(** val copy_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copy_loop src dst hi k =
  if bdec (ltb k hi)
  then copy_loop src (set dst k (get src k)) hi (add k (Uint63.of_int (1)))
  else dst

(** val msort :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort x a t lo hi =
  if bdec (splitc lo hi)
  then let (a1, t1) = msort x a t lo (midp lo hi) in
       let (a2, t2) = msort x a1 t1 (midp lo hi) hi in
       let t3 = merge_loop x a2 t2 (midp lo hi) hi lo (midp lo hi) lo in
       ((copy_loop t3 a2 hi lo), t3)
  else (a, t)

(** val fst_ch : string -> Uint63.t **)

let fst_ch w =
  get0 w (Uint63.of_int (0))

(** val lst_ch : string -> Uint63.t **)

let lst_ch w =
  get0 w (sub (length0 w) (Uint63.of_int (1)))

(** val build_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec build_loop x ord n nxt head k =
  if bdec (ltb k n)
  then let e = get ord (sub (sub n (Uint63.of_int (1))) k) in
       let c = fst_ch (get x e) in
       let h = get head c in
       build_loop x ord n (set nxt e h) (set head c e)
         (add k (Uint63.of_int (1)))
  else (nxt, head)

(** val deg_loop :
    string Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec deg_loop x n outd ind k =
  if bdec (ltb k n)
  then let a = fst_ch (get x k) in
       let b = lst_ch (get x k) in
       let oa = get outd a in
       let ib = get ind b in
       deg_loop x n (set outd a (add oa (Uint63.of_int (1))))
         (set ind b (add ib (Uint63.of_int (1)))) (add k (Uint63.of_int (1)))
  else (outd, ind)

(** val chk_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool -> ((Uint63.t * Uint63.t) * Uint63.t) * bool **)

let rec chk_loop outd ind c plus minus sv bad =
  if bdec (ltb c (Uint63.of_int (256)))
  then let o = get outd c in
       let i = get ind c in
       if eqb o i
       then chk_loop outd ind (add c (Uint63.of_int (1))) plus minus sv bad
       else if eqb o (add i (Uint63.of_int (1)))
            then chk_loop outd ind (add c (Uint63.of_int (1)))
                   (add plus (Uint63.of_int (1))) minus c bad
            else if eqb i (add o (Uint63.of_int (1)))
                 then chk_loop outd ind (add c (Uint63.of_int (1))) plus
                        (add minus (Uint63.of_int (1))) sv bad
                 else chk_loop outd ind (add c (Uint63.of_int (1))) plus
                        minus sv true
  else (((plus, minus), sv), bad)

(** val hier_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> string Marray.t
    -> Uint63.t -> string Marray.t * Uint63.t **)

let rec hier_loop x nxt n s ptr stk sp q res cnt =
  let v =
    if eqb sp (Uint63.of_int (0))
    then s
    else lst_ch (get x (get stk (sub sp (Uint63.of_int (1)))))
  in
  let p = get ptr v in
  if bdec ((&&) (ltb p n) (ltb q n))
  then let np = get nxt p in
       hier_loop x nxt n s (set ptr v np) (set stk sp p)
         (add sp (Uint63.of_int (1))) (add q (Uint63.of_int (1))) res cnt
  else if bdec (ltb (Uint63.of_int (0)) sp)
       then let e = get stk (sub sp (Uint63.of_int (1))) in
            hier_loop x nxt n s ptr stk (sub sp (Uint63.of_int (1))) q
              (set res (sub (sub n (Uint63.of_int (1))) cnt) (get x e))
              (add cnt (Uint63.of_int (1)))
       else (res, cnt)

(** val catenyms_impl : string Marray.t -> string Marray.t option **)

let catenyms_impl x =
  let n = length x in
  let ord0 = init_loop (make n (Uint63.of_int (0))) n (Uint63.of_int (0)) in
  let (ord, _) =
    msort x ord0 (make n (Uint63.of_int (0))) (Uint63.of_int (0)) n
  in
  let (nxt, head) =
    build_loop x ord n (make n (Uint63.of_int (0)))
      (make (Uint63.of_int (256)) n) (Uint63.of_int (0))
  in
  let (outd, ind) =
    deg_loop x n (make (Uint63.of_int (256)) (Uint63.of_int (0)))
      (make (Uint63.of_int (256)) (Uint63.of_int (0))) (Uint63.of_int (0))
  in
  let (p, bad) =
    chk_loop outd ind (Uint63.of_int (0)) (Uint63.of_int (0))
      (Uint63.of_int (0)) (Uint63.of_int (0)) false
  in
  let (p0, sv) = p in
  let (plus, minus) = p0 in
  if bad
  then None
  else if negb (eqb plus minus)
       then None
       else if negb (leb plus (Uint63.of_int (1)))
            then None
            else let s =
                   if eqb plus (Uint63.of_int (1))
                   then sv
                   else fst_ch (get x (get ord (Uint63.of_int (0))))
                 in
                 let (res, cnt) =
                   hier_loop x nxt n s head (make n (Uint63.of_int (0)))
                     (Uint63.of_int (0)) (Uint63.of_int (0))
                     (make n (make0 (Uint63.of_int (0)) (Uint63.of_int (0))))
                     (Uint63.of_int (0))
                 in
                 if eqb cnt n then Some res else None

(** val catenyms : string Marray.t -> string Marray.t option **)

let catenyms =
  catenyms_impl
