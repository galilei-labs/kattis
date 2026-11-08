
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

(** val gcd_loop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec gcd_loop a b =
  if bdec (eqb b (Uint63.of_int (0))) then a else gcd_loop b (mod0 a b)

(** val gcd63 : Uint63.t -> Uint63.t -> Uint63.t **)

let gcd63 =
  gcd_loop

(** val pow_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec pow_loop p base e acc =
  if bdec (eqb e (Uint63.of_int (0)))
  then acc
  else pow_loop p (mod0 (mul base base) p) (div e (Uint63.of_int (2)))
         (if eqb (mod0 e (Uint63.of_int (2))) (Uint63.of_int (0))
          then acc
          else mod0 (mul acc base) p)

(** val pow2mod : Uint63.t -> Uint63.t -> Uint63.t **)

let pow2mod p g =
  pow_loop p (Uint63.of_int (2)) g (Uint63.of_int (1))

(** val sum_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec sum_loop n m p d acc =
  if bdec (ltb d m)
  then sum_loop n m p (add d (Uint63.of_int (1)))
         (mod0
           (add acc
             (mod0
               (mul (sub m d)
                 (mod0
                   (sub (add (pow2mod p (gcd63 d n)) p) (Uint63.of_int (2)))
                   p))
               p))
           p)
  else acc

(** val derangement_rotations_impl : uint -> uint -> uint **)

let derangement_rotations_impl n p =
  sum_loop n (sub n (Uint63.of_int (1))) p (Uint63.of_int (1))
    (Uint63.of_int (0))

(** val derangement_rotations : uint -> uint -> uint **)

let derangement_rotations =
  derangement_rotations_impl
