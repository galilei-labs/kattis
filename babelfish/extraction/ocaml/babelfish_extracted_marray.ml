
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

(** val prime : Uint63.t **)

let prime =
  (Uint63.of_int (2147483647))

(** val hash_loop :
    Uint63.t -> string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec hash_loop a s len k acc =
  if bdec (ltb k len)
  then hash_loop a s len (add k (Uint63.of_int (1)))
         (mod0 (add (add (mul acc a) (get0 s k)) (Uint63.of_int (1))) prime)
  else acc

(** val hash : Uint63.t -> string -> Uint63.t **)

let hash a s =
  let len = length0 s in
  hash_loop a s len (Uint63.of_int (0)) (Uint63.of_int (0))

(** val seed : Uint63.t **)

let seed =
  (Uint63.of_int (88172645463325252))

(** val rng_next : Uint63.t -> Uint63.t **)

let rng_next st =
  add (mul st (Uint63.of_int (-2859235813007982803)))
    (Uint63.of_int (1442695040888963407))

(** val rng_draw : Uint63.t -> Uint63.t **)

let rng_draw st =
  add (mod0 (lsr0 st (Uint63.of_int (17))) (sub prime (Uint63.of_int (1))))
    (Uint63.of_int (1))

(** val count_loop :
    Uint63.t -> Uint63.t -> string Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t
    Marray.t **)

let rec count_loop a nb f n i cnt bk =
  if bdec (ltb i n)
  then let b = mod0 (hash a (get f i)) nb in
       count_loop a nb f n (add i (Uint63.of_int (1)))
         (set cnt b (add (get cnt b) (Uint63.of_int (1)))) (set bk i b)
  else (cnt, bk)

(** val sumsq_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec sumsq_loop cnt nb b acc =
  if bdec (ltb b nb)
  then sumsq_loop cnt nb (add b (Uint63.of_int (1)))
         (add acc (mul (get cnt b) (get cnt b)))
  else acc

(** val level1 :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> ((Uint63.t * Uint63.t) * Uint63.t
    Marray.t) * Uint63.t Marray.t **)

let rec level1 f n nb tries t st bk =
  let st' = rng_next st in
  let a = rng_draw st' in
  let (cnt, bk') =
    count_loop a nb f n (Uint63.of_int (0)) (make nb (Uint63.of_int (0))) bk
  in
  if bdec (ltb t tries)
  then if leb (sumsq_loop cnt nb (Uint63.of_int (0)) (Uint63.of_int (0)))
            (mul (Uint63.of_int (4)) n)
       then (((a, st'), cnt), bk')
       else level1 f n nb tries (add t (Uint63.of_int (1))) st' bk'
  else (((a, st'), cnt), bk')

(** val layout_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t **)

let rec layout_loop cnt nb b off st meta cur =
  if bdec (ltb b nb)
  then let c = get cnt b in
       layout_loop cnt nb (add b (Uint63.of_int (1))) (add off (mul c c))
         (add st c)
         (set (set meta (mul (Uint63.of_int (3)) b) off)
           (add (mul (Uint63.of_int (3)) b) (Uint63.of_int (1))) (mul c c))
         (set cur b st)
  else ((meta, cur), off)

(** val distribute :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec distribute bk n i cur order =
  if bdec (ltb i n)
  then let b = get bk i in
       let p = get cur b in
       distribute bk n (add i (Uint63.of_int (1)))
         (set cur b (add p (Uint63.of_int (1)))) (set order p i)
  else order

(** val place_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t * bool **)

let rec place_loop f order a off sz e i slot =
  if bdec (ltb i e)
  then let k = get order i in
       let s = add off (mod0 (hash a (get f k)) sz) in
       if eqb (get slot s) (Uint63.of_int (0))
       then place_loop f order a off sz e (add i (Uint63.of_int (1)))
              (set slot s (add k (Uint63.of_int (1))))
       else (slot, false)
  else (slot, true)

(** val clear_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec clear_loop e i slot =
  if bdec (ltb i e)
  then clear_loop e (add i (Uint63.of_int (1)))
         (set slot i (Uint63.of_int (0)))
  else slot

(** val level2 :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    (Uint63.t Marray.t * Uint63.t) * Uint63.t **)

let rec level2 f order st c off sz tries t rng slot =
  let rng' = rng_next rng in
  let a = rng_draw rng' in
  let (slot1, ok) = place_loop f order a off sz (add st c) st slot in
  if ok
  then ((slot1, a), rng')
  else if bdec (ltb t tries)
       then level2 f order st c off sz tries (add t (Uint63.of_int (1))) rng'
              (clear_loop (add off sz) off slot1)
       else ((slot1, a), rng')

(** val buckets_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec buckets_loop f order cnt nb b st rng meta slot =
  if bdec (ltb b nb)
  then let c = get cnt b in
       if eqb c (Uint63.of_int (0))
       then buckets_loop f order cnt nb (add b (Uint63.of_int (1))) st rng
              meta slot
       else let off = get meta (mul (Uint63.of_int (3)) b) in
            let sz =
              get meta (add (mul (Uint63.of_int (3)) b) (Uint63.of_int (1)))
            in
            let (p, rng') =
              level2 f order st c off sz (Uint63.of_int (64))
                (Uint63.of_int (0)) rng slot
            in
            let (slot', a) = p in
            buckets_loop f order cnt nb (add b (Uint63.of_int (1)))
              (add st c) rng'
              (set meta (add (mul (Uint63.of_int (3)) b) (Uint63.of_int (2)))
                a)
              slot'
  else (meta, slot)

type tables = { t_a1 : Uint63.t; t_nb : Uint63.t; t_meta : Uint63.t Marray.t;
                t_slot : Uint63.t Marray.t }

(** val build : string Marray.t -> Uint63.t -> tables **)

let build f n =
  let nb = if eqb n (Uint63.of_int (0)) then (Uint63.of_int (1)) else n in
  let (p, bk) =
    level1 f n nb (Uint63.of_int (32)) (Uint63.of_int (0)) seed
      (make n (Uint63.of_int (0)))
  in
  let (p0, cnt) = p in
  let (a1, rng) = p0 in
  let (p1, total) =
    layout_loop cnt nb (Uint63.of_int (0)) (Uint63.of_int (0))
      (Uint63.of_int (0))
      (make (mul (Uint63.of_int (3)) nb) (Uint63.of_int (0)))
      (make nb (Uint63.of_int (0)))
  in
  let (meta, cur) = p1 in
  let order =
    distribute bk n (Uint63.of_int (0)) cur (make n (Uint63.of_int (0)))
  in
  let (meta', slot) =
    buckets_loop f order cnt nb (Uint63.of_int (0)) (Uint63.of_int (0)) rng
      meta (make total (Uint63.of_int (0)))
  in
  { t_a1 = a1; t_nb = nb; t_meta = meta'; t_slot = slot }

(** val pos : tables -> string -> Uint63.t **)

let pos t x =
  let meta = t.t_meta in
  let b = mod0 (hash t.t_a1 x) t.t_nb in
  let sz = get meta (add (mul (Uint63.of_int (3)) b) (Uint63.of_int (1))) in
  if eqb sz (Uint63.of_int (0))
  then length t.t_slot
  else add (get meta (mul (Uint63.of_int (3)) b))
         (mod0
           (hash
             (get meta (add (mul (Uint63.of_int (3)) b) (Uint63.of_int (2))))
             x)
           sz)

(** val check_loop :
    tables -> string Marray.t -> Uint63.t -> Uint63.t -> bool **)

let rec check_loop t f n i =
  if bdec (ltb i n)
  then if eqb (get t.t_slot (pos t (get f i))) (add i (Uint63.of_int (1)))
       then check_loop t f n (add i (Uint63.of_int (1)))
       else false
  else true

(** val scan_loop :
    string Marray.t -> string -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec scan_loop f x n i =
  if bdec (ltb i n)
  then (match compare (get f i) x with
        | Eq -> i
        | _ -> scan_loop f x n (add i (Uint63.of_int (1))))
  else n

(** val query :
    string Marray.t -> string Marray.t -> Uint63.t -> bool -> tables ->
    string -> string option **)

let query e f n ok t x =
  let i =
    if ok
    then sub (get t.t_slot (pos t x)) (Uint63.of_int (1))
    else scan_loop f x n (Uint63.of_int (0))
  in
  if ltb i n
  then (match compare (get f i) x with
        | Eq -> Some (get e i)
        | _ -> None)
  else None

(** val fill_loop :
    string Marray.t -> string Marray.t -> string Marray.t -> Uint63.t -> bool
    -> tables -> Uint63.t -> Uint63.t -> string option Marray.t -> string
    option Marray.t **)

let rec fill_loop e f m n ok t l k out =
  if bdec (ltb k l)
  then fill_loop e f m n ok t l (add k (Uint63.of_int (1)))
         (set out k (query e f n ok t (get m k)))
  else out

(** val babelfish_impl :
    string Marray.t -> string Marray.t -> string Marray.t -> string option
    Marray.t **)

let babelfish_impl e f m =
  let n = length f in
  let t = build f n in
  let ok = check_loop t f n (Uint63.of_int (0)) in
  let l = length m in
  fill_loop e f m n ok t l (Uint63.of_int (0)) (make l None)

(** val babelfish :
    string Marray.t -> string Marray.t -> string Marray.t -> string option
    Marray.t **)

let babelfish =
  babelfish_impl
