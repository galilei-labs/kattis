
type comparison =
| Eq
| Lt
| Gt

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lor0 = Uint63.l_or

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

type relkind =
| IsA
| HasA

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

type pstr = string

(** val hloop : pstr -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec hloop s len i h =
  if bdec (ltb i len)
  then hloop s len (add i (Uint63.of_int (1)))
         (add (mul h (Uint63.of_int (31))) (get0 s i))
  else h

(** val hash : pstr -> Uint63.t **)

let hash s =
  let len = length0 s in
  land0 (hloop s len (Uint63.of_int (0)) (Uint63.of_int (0)))
    (Uint63.of_int (1023))

(** val walk :
    pstr -> pstr Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let rec walk s keys nxt p =
  if bdec (eqb p (Uint63.of_int (0)))
  then (Uint63.of_int (0))
  else (match compare (get keys (sub p (Uint63.of_int (1)))) s with
        | Eq -> p
        | _ ->
          let q = get nxt (sub p (Uint63.of_int (1))) in
          if bdec (ltb q p) then walk s keys nxt q else (Uint63.of_int (0)))

type ht = { hkeys : pstr Marray.t; hnxt : Uint63.t Marray.t;
            hhead : Uint63.t Marray.t; hcnt : Uint63.t }

(** val lookup : ht -> pstr -> Uint63.t **)

let lookup st s =
  let p = get st.hhead (hash s) in walk s st.hkeys st.hnxt p

(** val intern : ht -> pstr -> ht * Uint63.t **)

let intern st s =
  let b = hash s in
  let hb = get st.hhead b in
  let p = walk s st.hkeys st.hnxt hb in
  if eqb p (Uint63.of_int (0))
  then let c = st.hcnt in
       ({ hkeys = (set st.hkeys c s); hnxt = (set st.hnxt c hb); hhead =
       (set st.hhead b (add c (Uint63.of_int (1)))); hcnt =
       (add c (Uint63.of_int (1))) }, c)
  else (st, (sub p (Uint63.of_int (1))))

(** val iloop :
    pstr Marray.t -> pstr Marray.t -> Uint63.t -> Uint63.t -> ht -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> (ht * Uint63.t Marray.t) * Uint63.t
    Marray.t **)

let rec iloop xsrc xdst n i st ia ib =
  if bdec (ltb i n)
  then let (st1, a) = intern st (get xsrc i) in
       let (st2, b) = intern st1 (get xdst i) in
       iloop xsrc xdst n (add i (Uint63.of_int (1))) st2 (set ia i a)
         (set ib i b)
  else ((st, ia), ib)

(** val getbit :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let getbit t w u v =
  eqb
    (land0
      (lsr0 (get t (add (mul u w) (div v (Uint63.of_int (63)))))
        (mod0 v (Uint63.of_int (63))))
      (Uint63.of_int (1)))
    (Uint63.of_int (1))

(** val setbit :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let setbit t w u v =
  let i = add (mul u w) (div v (Uint63.of_int (63))) in
  set t i
    (lor0 (get t i) (lsl0 (Uint63.of_int (1)) (mod0 v (Uint63.of_int (63)))))

(** val eloop :
    relkind Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec eloop xrs ia ib k w n l t =
  if bdec (ltb l n)
  then let a = get ia l in
       let b = get ib l in
       let t' =
         match get xrs l with
         | IsA -> setbit (setbit t w a b) w (add a k) (add b k)
         | HasA -> setbit (setbit t w a (add b k)) w (add a k) (add b k)
       in
       eloop xrs ia ib k w n (add l (Uint63.of_int (1))) t'
  else t

(** val rowor :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec rowor t w u w0 j =
  if bdec (ltb j w)
  then rowor
         (set t (add (mul u w) j)
           (lor0 (get t (add (mul u w) j)) (get t (add (mul w0 w) j))))
         w u w0 (add j (Uint63.of_int (1)))
  else t

(** val fw_inner :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec fw_inner t n w w0 u =
  if bdec (ltb u n)
  then fw_inner
         (if getbit t w u w0 then rowor t w u w0 (Uint63.of_int (0)) else t)
         n w w0 (add u (Uint63.of_int (1)))
  else t

(** val fw_outer :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec fw_outer t n w w0 =
  if bdec (ltb w0 n)
  then fw_outer (fw_inner t n w w0 (Uint63.of_int (0))) n w
         (add w0 (Uint63.of_int (1)))
  else t

(** val fill :
    (Uint63.t -> bool) -> Uint63.t -> Uint63.t -> bool Marray.t -> bool
    Marray.t **)

let rec fill f m j out =
  if bdec (ltb j m)
  then fill f m (add j (Uint63.of_int (1))) (set out j (f j))
  else out

(** val answer :
    ht -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> pstr -> pstr ->
    relkind -> bool **)

let answer st t w k s1 s2 r =
  let a = lookup st s1 in
  let b = lookup st s2 in
  if eqb a (Uint63.of_int (0))
  then false
  else if eqb b (Uint63.of_int (0))
       then false
       else (match r with
             | IsA ->
               if eqb a b
               then true
               else getbit t w (sub a (Uint63.of_int (1)))
                      (sub b (Uint63.of_int (1)))
             | HasA ->
               getbit t w (sub a (Uint63.of_int (1)))
                 (add (sub b (Uint63.of_int (1))) k))

(** val isahasa_impl :
    pstr Marray.t -> relkind Marray.t -> pstr Marray.t -> pstr Marray.t ->
    relkind Marray.t -> pstr Marray.t -> bool Marray.t **)

let isahasa_impl xsrc xrs xdst xqsrc xqrs xqdst =
  let n = length xsrc in
  let cap = add n n in
  let st0 = { hkeys = (make cap (Pstring.unsafe_of_string "")); hnxt =
    (make cap (Uint63.of_int (0))); hhead =
    (make (Uint63.of_int (1024)) (Uint63.of_int (0))); hcnt =
    (Uint63.of_int (0)) }
  in
  let (p, ib) =
    iloop xsrc xdst n (Uint63.of_int (0)) st0 (make n (Uint63.of_int (0)))
      (make n (Uint63.of_int (0)))
  in
  let (st, ia) = p in
  let k = st.hcnt in
  let n0 = add k k in
  let w = div (add n0 (Uint63.of_int (62))) (Uint63.of_int (63)) in
  let t0 =
    eloop xrs ia ib k w n (Uint63.of_int (0))
      (make (mul n0 w) (Uint63.of_int (0)))
  in
  let t = fw_outer t0 n0 w (Uint63.of_int (0)) in
  let m = length xqsrc in
  fill (fun j -> answer st t w k (get xqsrc j) (get xqdst j) (get xqrs j)) m
    (Uint63.of_int (0)) (make m false)

(** val isahasa :
    string Marray.t -> relkind Marray.t -> string Marray.t -> string Marray.t
    -> relkind Marray.t -> string Marray.t -> bool Marray.t **)

let isahasa =
  isahasa_impl
