
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lor0 = Uint63.l_or

(** val lxor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lxor0 = Uint63.l_xor

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

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

(** val inner :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let rec inner s r rS lS rR lR aS aR rem =
  let w =
    lxor0
      (lor0 (lsr0 (get s aS) rS)
        (lsl0 (get s (add aS (Uint63.of_int (1)))) lS))
      (lor0 (lsr0 (get r aR) rR)
        (lsl0 (get r (add aR (Uint63.of_int (1)))) lR))
  in
  if bdec (leb rem (Uint63.of_int (63)))
  then negb
         (eqb
           (land0 w (sub (lsl0 (Uint63.of_int (1)) rem) (Uint63.of_int (1))))
           (Uint63.of_int (0)))
  else if eqb w (Uint63.of_int (0))
       then inner s r rS lS rR lR (add aS (Uint63.of_int (1)))
              (add aR (Uint63.of_int (1))) (sub rem (Uint63.of_int (63)))
       else true

(** val setbit : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let setbit t v =
  let a = div v (Uint63.of_int (63)) in
  set t a
    (lor0 (get t a) (lsl0 (Uint63.of_int (1)) (mod0 v (Uint63.of_int (63)))))

(** val scan :
    uint Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> bool **)

let rec scan x n s r pos =
  if bdec (ltb pos n)
  then let m = get x pos in
       let c = sub (sub n (Uint63.of_int (1))) m in
       let l = if ltb m c then m else c in
       let oS = add m (Uint63.of_int (1)) in
       let oR = sub n m in
       let rS = mod0 oS (Uint63.of_int (63)) in
       let rR = mod0 oR (Uint63.of_int (63)) in
       if inner s r rS (sub (Uint63.of_int (63)) rS) rR
            (sub (Uint63.of_int (63)) rR) (div oS (Uint63.of_int (63)))
            (div oR (Uint63.of_int (63))) l
       then false
       else scan x n (setbit s m) (setbit r c) (add pos (Uint63.of_int (1)))
  else true

(** val antiarithmetic_impl : uint Marray.t -> bool **)

let antiarithmetic_impl x =
  let n = length x in
  let k = add (div n (Uint63.of_int (63))) (Uint63.of_int (1)) in
  scan x n (make k (Uint63.of_int (0))) (make k (Uint63.of_int (0)))
    (Uint63.of_int (0))

(** val antiarithmetic : uint Marray.t -> bool **)

let antiarithmetic =
  antiarithmetic_impl
