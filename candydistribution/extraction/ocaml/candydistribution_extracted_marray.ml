
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

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val egcd_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec egcd_loop k a b sa sb =
  if bdec (eqb b (Uint63.of_int (0)))
  then (a, sa)
  else egcd_loop k b (mod0 a b) sb
         (mod0 (add sa (sub k (mod0 (mul (div a b) sb) k))) k)

(** val candy_impl : uint -> uint -> uint option **)

let candy_impl k c =
  let p =
    egcd_loop k k (mod0 c k) (Uint63.of_int (0)) (mod0 (Uint63.of_int (1)) k)
  in
  let g = fst p in
  let s = snd p in
  if eqb g (Uint63.of_int (1))
  then let b1 = if eqb s (Uint63.of_int (0)) then k else s in
       let b2 =
         if (&&) (eqb b1 (Uint63.of_int (1))) (eqb c (Uint63.of_int (1)))
         then add b1 k
         else b1
       in
       if leb b2 (Uint63.of_int (1000000000)) then Some b2 else None
  else None

module CandydistributionImpl =
 struct
  (** val candydistribution : uint -> uint -> uint option **)

  let candydistribution =
    candy_impl
 end
