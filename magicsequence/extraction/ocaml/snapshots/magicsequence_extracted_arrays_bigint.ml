
(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val k : Uint63.t **)

let k =
  (Uint63.of_int (65536))

(** val mask : Uint63.t **)

let mask =
  (Uint63.of_int (65535))

(** val gen_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    ((Uint63.t array * Uint63.t) * Uint63.t array) * Uint63.t array **)

let rec gen_loop a b c n i t m arr lo hi =
  if bdec (ltb i n)
  then let dl = land0 t mask in
       let dh = land0 (lsr0 t (Uint63.of_int (16))) mask in
       let kl = (fun a i -> Array.unsafe_get a (Uint63.hash i)) lo dl in
       let kh = (fun a i -> Array.unsafe_get a (Uint63.hash i)) hi dh in
       gen_loop a b c n (add i (Uint63.of_int (1)))
         (mod0 (add (mul t b) a) c) (if ltb m t then t else m)
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) arr i t)
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) lo dl
           (add kl (Uint63.of_int (1))))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) hi dh
           (add kh (Uint63.of_int (1))))
  else (((arr, m), lo), hi)

(** val prefix_loop :
    Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let rec prefix_loop e acc cnt =
  if bdec (ltb e k)
  then let k0 = (fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt e in
       prefix_loop (add e (Uint63.of_int (1))) (add acc k0)
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) cnt e acc)
  else cnt

(** val place_loop :
    Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t -> Uint63.t array ->
    Uint63.t array -> Uint63.t array **)

let rec place_loop s n src i cnt dst =
  if bdec (ltb i n)
  then let e = (fun a i -> Array.unsafe_get a (Uint63.hash i)) src i in
       let d = land0 (lsr0 e s) mask in
       let p = (fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt d in
       place_loop s n src (add i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) cnt d
           (add p (Uint63.of_int (1))))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) dst p e)
  else dst

(** val pass :
    Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t
    array -> Uint63.t array **)

let pass s n src cnt dst =
  let cnt0 = prefix_loop (Uint63.of_int (0)) (Uint63.of_int (0)) cnt in
  place_loop s n src (Uint63.of_int (0)) cnt0 dst

(** val hash_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    array -> Uint63.t **)

let rec hash_loop x y n i v r =
  if bdec (ltb i n)
  then hash_loop x y n (add i (Uint63.of_int (1)))
         (mod0
           (add (mul v x)
             ((fun a i -> Array.unsafe_get a (Uint63.hash i)) r i))
           y)
         r
  else v

(** val magic_impl :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let magic_impl n a b c x y =
  let (p, hi) =
    gen_loop a b c n (Uint63.of_int (0)) a (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))
      ((fun n d -> Array.make (Uint63.hash n) d) k (Uint63.of_int (0)))
      ((fun n d -> Array.make (Uint63.hash n) d) k (Uint63.of_int (0)))
  in
  let (p0, lo) = p in
  let (g, m) = p0 in
  let r1 =
    pass (Uint63.of_int (0)) n g lo
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))
  in
  let r = if ltb m k then r1 else pass (Uint63.of_int (16)) n r1 hi g in
  hash_loop x y n (Uint63.of_int (0)) (Uint63.of_int (0)) r

(** val magic : uint -> uint -> uint -> uint -> uint -> uint -> uint **)

let magic =
  magic_impl
