
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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val egcd_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec egcd_loop m r0 r1 s0 s1 =
  if bdec (eqb r1 (Uint63.of_int (0)))
  then (r0, s0)
  else egcd_loop m r1 (mod0 r0 r1) s1
         (mod0 (sub (add s0 m) (mod0 (mul (div r0 r1) s1) m)) m)

(** val crt_impl : uint -> uint -> uint -> uint -> (uint * uint) option **)

let crt_impl a n b m =
  let (g, s) =
    egcd_loop m n m (mod0 (Uint63.of_int (1)) m) (Uint63.of_int (0))
  in
  let mg = div m g in
  let d = mod0 (sub (add b m) (mod0 a m)) m in
  if eqb (mod0 d g) (Uint63.of_int (0))
  then let t = mod0 (mul (div d g) s) mg in
       Some ((add a (mul n t)), (mul n mg))
  else None

module GeneralchineseremainderImpl =
 struct
  (** val crt : uint -> uint -> uint -> uint -> (uint * uint) option **)

  let crt =
    crt_impl
 end
