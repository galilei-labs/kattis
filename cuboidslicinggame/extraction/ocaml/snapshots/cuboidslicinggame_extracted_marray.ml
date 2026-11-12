
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val lxor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lxor0 = Uint63.l_xor

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

type uint = Uint63.t

type player =
| Ruben
| Albert

(** val opponent : player -> player **)

let opponent = function
| Ruben -> Albert
| Albert -> Ruben

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val loop :
    (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let rec loop f hi i acc =
  if bdec (ltb i hi)
  then loop f hi (add i (Uint63.of_int (1))) (f i acc)
  else acc

(** val for_ :
    (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let for_ f lo hi acc =
  loop f hi lo acc

(** val imin : Uint63.t -> Uint63.t -> Uint63.t **)

let imin a b =
  if leb a b then a else b

(** val imax : Uint63.t -> Uint63.t -> Uint63.t **)

let imax a b =
  if leb a b then b else a

(** val cidx : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let cidx d x y z =
  add (mul (add (mul x d) y) d) z

(** val look :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let look t d x y z =
  let lo = imin x (imin y z) in
  let hi = imax x (imax y z) in
  get t (cidx d lo (sub (sub (add (add x y) z) lo) hi) hi)

(** val cutv :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let cutv t d x y z a b c =
  let p1 = sub a (Uint63.of_int (1)) in
  let p2 = sub x a in
  let q1 = sub b (Uint63.of_int (1)) in
  let q2 = sub y b in
  let r1 = sub c (Uint63.of_int (1)) in
  let r2 = sub z c in
  lxor0 (look t d p1 q1 r1)
    (lxor0 (look t d p1 q1 r2)
      (lxor0 (look t d p1 q2 r1)
        (lxor0 (look t d p1 q2 r2)
          (lxor0 (look t d p2 q1 r1)
            (lxor0 (look t d p2 q1 r2)
              (lxor0 (look t d p2 q2 r1) (look t d p2 q2 r2)))))))

(** val mark_c :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let mark_c t d x y z a b hc st s =
  for_ (fun c s0 -> set s0 (cutv t d x y z a b c) st) (Uint63.of_int (1))
    (add hc (Uint63.of_int (1))) s

(** val mark_b :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let mark_b t d x y z a hb hc st s =
  for_ (fun b s0 -> mark_c t d x y z a b hc st s0) (Uint63.of_int (1))
    (add hb (Uint63.of_int (1))) s

(** val mark_a :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let mark_a t d x y z ha hb hc st s =
  for_ (fun a s0 -> mark_b t d x y z a hb hc st s0) (Uint63.of_int (1))
    (add ha (Uint63.of_int (1))) s

(** val mex_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec mex_loop s st l t =
  if bdec (ltb t l)
  then if eqb (get s t) st
       then mex_loop s st l (add t (Uint63.of_int (1)))
       else t
  else t

(** val cell :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t
    Marray.t * Uint63.t Marray.t) -> Uint63.t Marray.t * Uint63.t Marray.t **)

let cell d l x y z = function
| (t, seen) ->
  let k = cidx d x y z in
  let stamp = add k (Uint63.of_int (1)) in
  let seen0 =
    mark_a t d x y z (div (add x (Uint63.of_int (1))) (Uint63.of_int (2)))
      (div (add y (Uint63.of_int (1))) (Uint63.of_int (2)))
      (div (add z (Uint63.of_int (1))) (Uint63.of_int (2))) stamp seen
  in
  let m = mex_loop seen0 stamp l (Uint63.of_int (0)) in ((set t k m), seen0)

(** val table :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let table d l =
  for_ (fun x st ->
    for_ (fun y st0 -> for_ (fun z st1 -> cell d l x y z st1) y d st0) x d st)
    (Uint63.of_int (1)) d ((make l (Uint63.of_int (0))),
    (make l (Uint63.of_int (0))))

(** val winner_impl :
    player -> uint Marray.t -> uint Marray.t -> uint Marray.t -> player **)

let winner_impl s xs ys zs =
  let n = length xs in
  let m =
    for_ (fun i m -> imax m (imax (get xs i) (imax (get ys i) (get zs i))))
      (Uint63.of_int (0)) n (Uint63.of_int (0))
  in
  let d = add m (Uint63.of_int (1)) in
  let l = mul (mul d d) d in
  let t = fst (table d l) in
  let gx =
    for_ (fun i acc -> lxor0 acc (look t d (get xs i) (get ys i) (get zs i)))
      (Uint63.of_int (0)) n (Uint63.of_int (0))
  in
  if eqb gx (Uint63.of_int (0)) then opponent s else s

(** val winner :
    player -> uint Marray.t -> uint Marray.t -> uint Marray.t -> player **)

let winner =
  winner_impl
