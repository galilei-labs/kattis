
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

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

(** val rotd : Uint63.t -> Uint63.t option **)

let rotd d =
  if eqb d (Uint63.of_int (0))
  then Some (Uint63.of_int (0))
  else if eqb d (Uint63.of_int (1))
       then Some (Uint63.of_int (1))
       else if eqb d (Uint63.of_int (2))
            then Some (Uint63.of_int (2))
            else if eqb d (Uint63.of_int (5))
                 then Some (Uint63.of_int (5))
                 else if eqb d (Uint63.of_int (6))
                      then Some (Uint63.of_int (9))
                      else if eqb d (Uint63.of_int (8))
                           then Some (Uint63.of_int (8))
                           else if eqb d (Uint63.of_int (9))
                                then Some (Uint63.of_int (6))
                                else None

(** val rloop : Uint63.t -> Uint63.t -> Uint63.t option **)

let rec rloop x r =
  if bdec (ltb (Uint63.of_int (0)) x)
  then (match rotd (mod0 x (Uint63.of_int (10))) with
        | Some e ->
          rloop (div x (Uint63.of_int (10)))
            (add (mul r (Uint63.of_int (10))) e)
        | None -> None)
  else Some r

(** val alt : Uint63.t -> Uint63.t **)

let alt c =
  match rloop c (Uint63.of_int (0)) with
  | Some r -> r
  | None -> c

(** val k : Uint63.t **)

let k =
  (Uint63.of_int (131072))

(** val build :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec build y t n i =
  if bdec (ltb i n)
  then let c = get y i in
       build y
         (set (set t (mul (Uint63.of_int (2)) i) (add (mul c k) i))
           (add (mul (Uint63.of_int (2)) i) (Uint63.of_int (1)))
           (add (mul (alt c) k) i))
         n (add i (Uint63.of_int (1)))
  else t

(** val merge_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec merge_loop src dst i mid j hi k0 =
  if bdec (ltb k0 hi)
  then if ltb i mid
       then if ltb j hi
            then if leb (get src i) (get src j)
                 then merge_loop src (set dst k0 (get src i))
                        (add i (Uint63.of_int (1))) mid j hi
                        (add k0 (Uint63.of_int (1)))
                 else merge_loop src (set dst k0 (get src j)) i mid
                        (add j (Uint63.of_int (1))) hi
                        (add k0 (Uint63.of_int (1)))
            else merge_loop src (set dst k0 (get src i))
                   (add i (Uint63.of_int (1))) mid j hi
                   (add k0 (Uint63.of_int (1)))
       else merge_loop src (set dst k0 (get src j)) i mid
              (add j (Uint63.of_int (1))) hi (add k0 (Uint63.of_int (1)))
  else dst

(** val copy_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copy_loop src dst hi k0 =
  if bdec (ltb k0 hi)
  then copy_loop src (set dst k0 (get src k0)) hi (add k0 (Uint63.of_int (1)))
  else dst

(** val msort :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort a b lo hi =
  if bdec (ltb lo hi)
  then if bdec (ltb (Uint63.of_int (1)) (sub hi lo))
       then let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
            let (a1, b1) = msort a b lo mid in
            let (a2, b2) = msort a1 b1 mid hi in
            let b3 = merge_loop a2 b2 lo mid mid hi lo in
            ((copy_loop b3 a2 hi lo), b3)
       else (a, b)
  else (a, b)

(** val lbloop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec lbloop s x lo hi =
  if bdec (ltb lo hi)
  then if ltb (get s (add lo (div (sub hi lo) (Uint63.of_int (2))))) x
       then lbloop s x
              (add (add lo (div (sub hi lo) (Uint63.of_int (2))))
                (Uint63.of_int (1)))
              hi
       else lbloop s x lo (add lo (div (sub hi lo) (Uint63.of_int (2))))
  else lo

(** val inrange :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let inrange s m lo hi =
  let p = lbloop s lo (Uint63.of_int (0)) m in
  if ltb p m then ltb (get s p) hi else false

(** val found :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let found s m w i =
  if inrange s m (mul w k) (add (mul w k) i)
  then true
  else inrange s m (add (add (mul w k) i) (Uint63.of_int (1)))
         (mul (add w (Uint63.of_int (1))) k)

(** val okv :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let okv s m s0 v i =
  if leb v s0 then found s m (sub s0 v) i else false

(** val scan :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let rec scan y s s0 m n i =
  if bdec (ltb i n)
  then let c = get y i in
       if okv s m s0 c i
       then true
       else if okv s m s0 (alt c) i
            then true
            else scan y s s0 m n (add i (Uint63.of_int (1)))
  else false

(** val addemup_impl : uint -> uint Marray.t -> bool **)

let addemup_impl s y =
  let n = length y in
  let m = mul (Uint63.of_int (2)) n in
  let t = build y (make m (Uint63.of_int (0))) n (Uint63.of_int (0)) in
  let s0 = fst (msort t (make m (Uint63.of_int (0))) (Uint63.of_int (0)) m) in
  scan y s0 s m n (Uint63.of_int (0))

(** val addemup : uint -> uint Marray.t -> bool **)

let addemup =
  addemup_impl
