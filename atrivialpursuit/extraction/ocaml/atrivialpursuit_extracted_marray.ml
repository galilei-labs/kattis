
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val mulc : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let mulc = Uint63.mulc

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

(** val diveucl_21 :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let diveucl_21 = Uint63.div21

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val lIM : Uint63.t **)

let lIM =
  (Uint63.of_int (1000000))

(** val mulmod : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let mulmod a b n =
  let (h, l) = mulc a b in snd (diveucl_21 h l n)

(** val pow_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec pow_loop b e r n =
  if bdec (ltb (Uint63.of_int (0)) e)
  then pow_loop (mulmod b b n) (lsr0 e (Uint63.of_int (1)))
         (if eqb (land0 e (Uint63.of_int (1))) (Uint63.of_int (1))
          then mulmod r b n
          else r)
         n
  else r

(** val powmod : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let powmod b e n =
  pow_loop (mod0 b n) e (mod0 (Uint63.of_int (1)) n) n

(** val gcd_loop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec gcd_loop a b =
  if bdec (ltb (Uint63.of_int (0)) b) then gcd_loop b (mod0 a b) else a

(** val igcd : Uint63.t -> Uint63.t -> Uint63.t **)

let igcd =
  gcd_loop

(** val isq_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec isq_loop x s w =
  if bdec (ltb (Uint63.of_int (1)) w)
  then let b = lsr0 w (Uint63.of_int (1)) in
       let t = add s b in
       if leb (mul t t) x then isq_loop x t (sub w b) else isq_loop x s b
  else s

(** val isqrt : Uint63.t -> Uint63.t **)

let isqrt x =
  isq_loop x (Uint63.of_int (0)) (Uint63.of_int (2147483648))

(** val divfull : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let rec divfull x c k =
  if bdec (ltb (Uint63.of_int (0)) c)
  then if eqb (mod0 c x) (Uint63.of_int (0))
       then divfull x (div c x) (add k (Uint63.of_int (1)))
       else (c, k)
  else (c, k)

(** val divpass :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t **)

let rec divpass x a n j e =
  if bdec (ltb j n)
  then let c = get a j in
       if eqb (mod0 c x) (Uint63.of_int (0))
       then let ck = divfull x c (Uint63.of_int (0)) in
            divpass x (set a j (fst ck)) n (add j (Uint63.of_int (1)))
              (add e (snd ck))
       else divpass x a n (add j (Uint63.of_int (1))) e
  else (a, e)

(** val mark_loop : bool Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t **)

let rec mark_loop m i j =
  if bdec (ltb j lIM) then mark_loop (set m j true) i (add j i) else m

(** val sieve_loop :
    bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t **)

let rec sieve_loop m pr np i =
  if bdec (ltb i lIM)
  then if get m i
       then sieve_loop m pr np (add i (Uint63.of_int (1)))
       else if bdec ((&&) (ltb (Uint63.of_int (0)) i) (ltb i lIM))
            then sieve_loop (mark_loop m i (add i i)) (set pr np i)
                   (add np (Uint63.of_int (1))) (add i (Uint63.of_int (1)))
            else (pr, np)
  else (pr, np)

(** val sieve : Uint63.t Marray.t * Uint63.t **)

let sieve =
  sieve_loop (make lIM false) (make lIM (Uint63.of_int (0)))
    (Uint63.of_int (0)) (Uint63.of_int (2))

(** val strip2 : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let rec strip2 d s =
  if bdec
       ((&&) (ltb (Uint63.of_int (0)) d)
         (eqb (land0 d (Uint63.of_int (1))) (Uint63.of_int (0))))
  then strip2 (lsr0 d (Uint63.of_int (1))) (add s (Uint63.of_int (1)))
  else (d, s)

(** val mr_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let rec mr_loop n y i s =
  if bdec (ltb i s)
  then if eqb y (sub n (Uint63.of_int (1)))
       then false
       else let y' = mulmod y y n in
            if eqb y' (Uint63.of_int (1))
            then true
            else mr_loop n y' (add i (Uint63.of_int (1))) s
  else true

(** val mr_base : Uint63.t -> Uint63.t -> bool **)

let mr_base n a =
  let (d, s) = strip2 (sub n (Uint63.of_int (1))) (Uint63.of_int (0)) in
  let y = powmod a d n in
  if eqb y (Uint63.of_int (1))
  then false
  else mr_loop n y (Uint63.of_int (0)) s

(** val mr_comp : Uint63.t -> bool **)

let mr_comp n =
  (||)
    ((||)
      ((||)
        ((||)
          ((||)
            ((||)
              ((||)
                ((||)
                  ((||)
                    ((||)
                      ((||) (mr_base n (Uint63.of_int (2)))
                        (mr_base n (Uint63.of_int (3))))
                      (mr_base n (Uint63.of_int (5))))
                    (mr_base n (Uint63.of_int (7))))
                  (mr_base n (Uint63.of_int (11))))
                (mr_base n (Uint63.of_int (13))))
              (mr_base n (Uint63.of_int (17))))
            (mr_base n (Uint63.of_int (19))))
          (mr_base n (Uint63.of_int (23))))
        (mr_base n (Uint63.of_int (29))))
      (mr_base n (Uint63.of_int (31))))
    (mr_base n (Uint63.of_int (37)))

type bres =
| BFound
| BComp
| BFail

(** val aLIM : Uint63.t **)

let aLIM =
  (Uint63.of_int (1000))

(** val find_base : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bres **)

let rec find_base n m q a =
  if bdec (ltb a aLIM)
  then if negb (eqb (powmod a m n) (Uint63.of_int (1)))
       then BComp
       else let u = powmod a (div m q) n in
            let g = igcd (mod0 (sub (add u n) (Uint63.of_int (1))) n) n in
            if eqb g (Uint63.of_int (1))
            then BFound
            else if ltb g n
                 then BComp
                 else find_base n m q (add a (Uint63.of_int (1)))
  else BFail

(** val td_cert :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> (bres * Uint63.t) * Uint63.t **)

let rec td_cert pr np k n m f r =
  if bdec (ltb k np)
  then if ltb (div n f) f
       then ((BFound, f), r)
       else let q = get pr k in
            if eqb (mod0 r q) (Uint63.of_int (0))
            then if bdec (ltb (Uint63.of_int (1)) q)
                 then let rk = divfull q r (Uint63.of_int (0)) in
                      (match find_base n m q (Uint63.of_int (2)) with
                       | BFound ->
                         td_cert pr np (add k (Uint63.of_int (1))) n m
                           (mul f (div r (fst rk))) (fst rk)
                       | x -> ((x, f), r))
                 else ((BFail, f), r)
            else td_cert pr np (add k (Uint63.of_int (1))) n m f r
  else ((BFound, f), r)

(** val rho_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec rho_loop n c x y q j r b budget =
  if bdec (ltb (Uint63.of_int (0)) budget)
  then let y' = mod0 (add (mulmod y y n) c) n in
       let diff = if ltb x y' then sub y' x else sub x y' in
       let q' = mulmod q diff n in
       let b' = add b (Uint63.of_int (1)) in
       let g =
         if eqb b' (Uint63.of_int (128))
         then igcd q' n
         else (Uint63.of_int (1))
       in
       if negb (eqb g (Uint63.of_int (1)))
       then g
       else let b'' =
              if eqb b' (Uint63.of_int (128)) then (Uint63.of_int (0)) else b'
            in
            let j' = add j (Uint63.of_int (1)) in
            if eqb j' r
            then rho_loop n c y' y' q' (Uint63.of_int (0)) (add r r) b''
                   (sub budget (Uint63.of_int (1)))
            else rho_loop n c x y' q' j' r b''
                   (sub budget (Uint63.of_int (1)))
  else (Uint63.of_int (1))

(** val rHOC : Uint63.t **)

let rHOC =
  (Uint63.of_int (40))

(** val rho_try : Uint63.t -> Uint63.t -> Uint63.t **)

let rec rho_try n c =
  if bdec (ltb c rHOC)
  then let g =
         rho_loop n c (Uint63.of_int (2)) (Uint63.of_int (2))
           (Uint63.of_int (1)) (Uint63.of_int (0)) (Uint63.of_int (1))
           (Uint63.of_int (0)) (Uint63.of_int (1048576))
       in
       if (&&) ((&&) (ltb (Uint63.of_int (1)) g) (ltb g n))
            (eqb (mod0 n g) (Uint63.of_int (0)))
       then g
       else rho_try n (add c (Uint63.of_int (1)))
  else (Uint63.of_int (0))

type cres =
| CPrime
| CComp
| CFail

(** val t12 : Uint63.t **)

let t12 =
  (Uint63.of_int (1000000000000))

(** val base_res : bres -> cres **)

let base_res = function
| BFound -> CPrime
| BComp -> CComp
| BFail -> CFail

(** val certify : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> cres **)

let rec certify pr np n =
  let m = sub n (Uint63.of_int (1)) in
  let (p, r) = td_cert pr np (Uint63.of_int (0)) n m (Uint63.of_int (1)) m in
  let (b, f) = p in
  (match b with
   | BFound ->
     if ltb (div n f) f
     then CPrime
     else if leb r (Uint63.of_int (1))
          then CFail
          else if leb r t12
               then base_res (find_base n m r (Uint63.of_int (2)))
               else if mr_comp r
                    then let g = rho_try r (Uint63.of_int (1)) in
                         if (&&) ((&&) (ltb (Uint63.of_int (1)) g) (ltb g r))
                              (eqb (mod0 r g) (Uint63.of_int (0)))
                         then (match find_base n m g (Uint63.of_int (2)) with
                               | BFound ->
                                 let f' = mul f g in
                                 if ltb (div n f') f'
                                 then CPrime
                                 else base_res
                                        (find_base n m (div r g)
                                          (Uint63.of_int (2)))
                               | BComp -> CComp
                               | BFail -> CFail)
                         else CFail
                    else if bdec (ltb r n)
                         then (match certify pr np r with
                               | CPrime ->
                                 base_res
                                   (find_base n m r (Uint63.of_int (2)))
                               | _ -> CFail)
                         else CFail
   | BComp -> CComp
   | BFail -> CFail)

(** val td_loop : Uint63.t -> Uint63.t -> bool **)

let rec td_loop n d =
  if bdec (ltb d n)
  then if leb (mul d d) n
       then if eqb (mod0 n d) (Uint63.of_int (0))
            then false
            else td_loop n (add d (Uint63.of_int (1)))
       else true
  else true

type kind =
| KPrime
| KSquare
| KSemi

(** val classify : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> kind **)

let classify pr np x =
  if leb x t12
  then KPrime
  else let s = isqrt x in
       if eqb (mul s s) x
       then KSquare
       else if mr_comp x
            then KSemi
            else (match certify pr np x with
                  | CPrime -> KPrime
                  | CComp -> KSemi
                  | CFail ->
                    if td_loop x (Uint63.of_int (2)) then KPrime else KSemi)

(** val mODP : Uint63.t **)

let mODP =
  (Uint63.of_int (1000000007))

(** val fmod : Uint63.t -> Uint63.t -> Uint63.t **)

let fmod e p =
  let a = powmod (add e (Uint63.of_int (1))) p mODP in
  let b = powmod e p mODP in
  let c = powmod (sub e (Uint63.of_int (1))) p mODP in
  mod0 (add (add a (mul (Uint63.of_int (2)) (sub mODP b))) c) mODP

(** val contrib :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let contrib pr np x e p =
  match classify pr np x with
  | KPrime -> fmod e p
  | KSquare -> fmod (add e e) p
  | KSemi -> let f = fmod e p in mulmod f f mODP

(** val step_acc :
    Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t) -> Uint63.t **)

let step_acc acc eg el f =
  if eqb eg el
  then acc
  else if ltb el eg
       then (Uint63.of_int (0))
       else mulmod acc (f (sub el eg)) mODP

(** val ph1 :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec ph1 pr np k aG aL nG nL p acc =
  if bdec (ltb k np)
  then let p0 = get pr k in
       if bdec (ltb (Uint63.of_int (1)) p0)
       then let rG = divpass p0 aG nG (Uint63.of_int (0)) (Uint63.of_int (0))
            in
            let rL = divpass p0 aL nL (Uint63.of_int (0)) (Uint63.of_int (0))
            in
            ph1 pr np (add k (Uint63.of_int (1))) (fst rG) (fst rL) nG nL p
              (step_acc acc (snd rG) (snd rL) (fun e -> fmod e p))
       else ((aG, aL), acc)
  else ((aG, aL), acc)

(** val refine :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec refine a n j x =
  if bdec (ltb j n)
  then let d = igcd x (get a j) in
       refine a n (add j (Uint63.of_int (1)))
         (if (&&) (ltb (Uint63.of_int (1)) d) (ltb d x) then d else x)
  else x

(** val sel_get :
    bool -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let sel_get sel aG aL i =
  if sel then get aL i else get aG i

(** val peel :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> bool -> Uint63.t -> Uint63.t -> Uint63.t ->
    (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec peel pr np aG aL nG nL sel i p acc =
  let c = sel_get sel aG aL i in
  if bdec (ltb (Uint63.of_int (1)) c)
  then let x =
         refine aL nL (Uint63.of_int (0)) (refine aG nG (Uint63.of_int (0)) c)
       in
       if bdec (ltb (Uint63.of_int (1)) x)
       then let rG = divpass x aG nG (Uint63.of_int (0)) (Uint63.of_int (0))
            in
            let rL = divpass x aL nL (Uint63.of_int (0)) (Uint63.of_int (0))
            in
            let acc' =
              step_acc acc (snd rG) (snd rL) (fun e -> contrib pr np x e p)
            in
            if bdec (ltb (sel_get sel (fst rG) (fst rL) i) c)
            then peel pr np (fst rG) (fst rL) nG nL sel i p acc'
            else (((fst rG), (fst rL)), acc')
       else ((aG, aL), acc)
  else ((aG, aL), acc)

(** val ph2 :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> bool -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec ph2 pr np aG aL nG nL sel n i p acc =
  if bdec (ltb i n)
  then let r = peel pr np aG aL nG nL sel i p acc in
       ph2 pr np (fst (fst r)) (snd (fst r)) nG nL sel n
         (add i (Uint63.of_int (1))) p (snd r)
  else ((aG, aL), acc)

(** val atp_impl : uint -> uint Marray.t -> uint Marray.t -> uint **)

let atp_impl p x y =
  let pr = fst sieve in
  let np = snd sieve in
  let nG = length x in
  let nL = length y in
  let r1 =
    ph1 pr np (Uint63.of_int (0)) (copy x) (copy y) nG nL p
      (Uint63.of_int (1))
  in
  let r2 =
    ph2 pr np (fst (fst r1)) (snd (fst r1)) nG nL false nG
      (Uint63.of_int (0)) p (snd r1)
  in
  let r3 =
    ph2 pr np (fst (fst r2)) (snd (fst r2)) nG nL true nL (Uint63.of_int (0))
      p (snd r2)
  in
  snd r3

(** val atrivialpursuit : uint -> uint Marray.t -> uint Marray.t -> uint **)

let atrivialpursuit =
  atp_impl
