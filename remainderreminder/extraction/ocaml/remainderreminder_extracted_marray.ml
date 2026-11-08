
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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val vol : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let vol a b x =
  mul (mul x (sub a (mul (Uint63.of_int (2)) x)))
    (sub b (mul (Uint63.of_int (2)) x))

(** val upd :
    ((Uint63.t * Uint63.t) * Uint63.t) -> Uint63.t ->
    (Uint63.t * Uint63.t) * Uint63.t **)

let upd t v =
  let (p, t3) = t in
  let (t1, t2) = p in
  if ltb t1 v
  then ((v, t1), t2)
  else if eqb v t1
       then t
       else if ltb t2 v
            then ((t1, v), t2)
            else if eqb v t2 then t else if ltb t3 v then ((t1, t2), v) else t

(** val scan :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    ((Uint63.t * Uint63.t) * Uint63.t) -> (Uint63.t * Uint63.t) * Uint63.t **)

let rec scan a b m x t =
  if bdec (ltb x m)
  then scan a b m (add x (Uint63.of_int (1))) (upd t (vol a b x))
  else t

(** val egcd :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec egcd m r0 s0 r1 s1 =
  if bdec (eqb r1 (Uint63.of_int (0)))
  then (r0, s0)
  else egcd m r1 s1 (mod0 r0 r1)
         (mod0 (sub (add s0 m) (mod0 (mul (mod0 (div r0 r1) m) s1) m)) m)

(** val merge :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let merge r1 m1 r2 m2 =
  let (g, s) = egcd m2 m1 (mod0 (Uint63.of_int (1)) m2) m2 (Uint63.of_int (0))
  in
  let dd = mod0 (sub (add r2 m2) (mod0 r1 m2)) m2 in
  if eqb (mod0 dd g) (Uint63.of_int (0))
  then let m2' = div m2 g in
       ((add r1 (mul m1 (mod0 (mul (div dd g) s) m2'))), (mul m1 m2'))
  else ((Uint63.of_int (0)), (Uint63.of_int (0)))

(** val lift : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let lift f r l =
  add f (mod0 (sub (add r l) (mod0 f l)) l)

(** val rr_impl :
    uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint **)

let rr_impl a b c d e f _ =
  let m = div (add a (Uint63.of_int (1))) (Uint63.of_int (2)) in
  let (p, v3) =
    scan a b m (Uint63.of_int (1)) (((Uint63.of_int (0)),
      (Uint63.of_int (0))), (Uint63.of_int (0)))
  in
  let (v1, v2) = p in
  let (r12, l12) = merge c v1 d v2 in
  let (r, l) = merge r12 l12 e v3 in lift f r l

(** val remainderreminder :
    uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint **)

let remainderreminder =
  rr_impl
