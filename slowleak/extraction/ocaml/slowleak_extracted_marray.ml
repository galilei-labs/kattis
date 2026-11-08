
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

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (2305843009213693952))

(** val setmin :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let setmin t p s =
  if ltb s (get t p) then set t p s else t

(** val diag_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec diag_loop n i t =
  if bdec (ltb i n)
  then diag_loop n (add i (Uint63.of_int (1)))
         (set t (add (mul i n) i) (Uint63.of_int (0)))
  else t

(** val edge_loop :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec edge_loop n xi xj xk m e t =
  if bdec (ltb e m)
  then let u = sub (get xi e) (Uint63.of_int (1)) in
       let v = sub (get xj e) (Uint63.of_int (1)) in
       let k = get xk e in
       edge_loop n xi xj xk m (add e (Uint63.of_int (1)))
         (setmin (setmin t (add (mul u n) v) k) (add (mul v n) u) k)
  else t

(** val fw_j :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec fw_j n rowi rowk aik j t =
  if bdec (ltb j n)
  then fw_j n rowi rowk aik (add j (Uint63.of_int (1)))
         (setmin t (add rowi j) (add aik (get t (add rowk j))))
  else t

(** val fw_i :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec fw_i n k rowk i t =
  if bdec (ltb i n)
  then let rowi = mul i n in
       fw_i n k rowk (add i (Uint63.of_int (1)))
         (fw_j n rowi rowk (get t (add rowi k)) (Uint63.of_int (0)) t)
  else t

(** val fw_k :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec fw_k n k t =
  if bdec (ltb k n)
  then fw_k n (add k (Uint63.of_int (1)))
         (fw_i n k (mul k n) (Uint63.of_int (0)) t)
  else t

(** val vx_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec vx_loop xs t i v =
  if bdec (ltb i t)
  then vx_loop xs t (add i (Uint63.of_int (1)))
         (set v (add i (Uint63.of_int (1)))
           (sub (get xs i) (Uint63.of_int (1))))
  else v

(** val sel_loop :
    Uint63.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec sel_loop m vis dist i b bv =
  if bdec (ltb i m)
  then if get vis i
       then sel_loop m vis dist (add i (Uint63.of_int (1))) b bv
       else let di = get dist i in
            if ltb di bv
            then sel_loop m vis dist (add i (Uint63.of_int (1))) i di
            else sel_loop m vis dist (add i (Uint63.of_int (1))) b bv
  else b

(** val rel_loop :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec rel_loop m v t vis d ru du b dist =
  if bdec (ltb b m)
  then let dist' =
         if get vis b
         then dist
         else let w = get t (add ru (get v b)) in
              if leb w d then setmin dist b (add du w) else dist
       in
       rel_loop m v t vis d ru du (add b (Uint63.of_int (1))) dist'
  else dist

(** val dij_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t -> Uint63.t Marray.t ->
    Uint63.t option **)

let rec dij_loop n m tgt v t d r vis dist =
  if bdec (ltb (Uint63.of_int (0)) r)
  then let u = sel_loop m vis dist (Uint63.of_int (0)) m iNF in
       if eqb u m
       then None
       else if eqb u tgt
            then Some (get dist u)
            else let vis' = set vis u true in
                 let dist' =
                   rel_loop m v t vis' d (mul (get v u) n) (get dist u)
                     (Uint63.of_int (0)) dist
                 in
                 dij_loop n m tgt v t d (sub r (Uint63.of_int (1))) vis' dist'
  else None

(** val slowleak_impl :
    uint -> uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint
    Marray.t -> uint option **)

let slowleak_impl x y xs xi xj xk =
  let t0 = diag_loop x (Uint63.of_int (0)) (make (mul x x) iNF) in
  let m = length xi in
  let t1 = edge_loop x xi xj xk m (Uint63.of_int (0)) t0 in
  let t = fw_k x (Uint63.of_int (0)) t1 in
  let t2 = length xs in
  let m0 = add t2 (Uint63.of_int (2)) in
  let v =
    vx_loop xs t2 (Uint63.of_int (0))
      (set (make m0 (Uint63.of_int (0))) (add t2 (Uint63.of_int (1)))
        (sub x (Uint63.of_int (1))))
  in
  dij_loop x m0 (add t2 (Uint63.of_int (1))) v t y m0 (make m0 false)
    (set (make m0 iNF) (Uint63.of_int (0)) (Uint63.of_int (0)))

(** val slowleak :
    uint -> uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint
    Marray.t -> uint option **)

let slowleak =
  slowleak_impl
