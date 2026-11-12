(* tools/bigint.ml -- pure-OCaml arbitrary-precision integers for Kattis
   submissions whose extracted code uses Rocq's [positive], [N] or [Z].

   Kattis compiles OCaml with exactly
   `ocamlopt -o exe -I +unix -I +str unix.cmxa str.cmxa file`: no findlib,
   hence no Zarith, which the stock ExtrOcamlZBigInt targets.  This module
   replaces it.  lib/ExtrZBigint.v is the extraction configuration
   (the counterpart of ExtrOcamlZBigInt.v) that maps [positive], [N], [Z]
   and their usual operations onto [Bigint]; this file is pasted into the
   submission before the extracted code (see tools/README_bigint.md).
   Standard library only (no Str, no Unix, no C stubs), OCaml 4.14 and 5.x.

   Representation: sign-magnitude.  [sign] is -1, 0 or 1; [mag] is the
   absolute value, little-endian limbs in base 2^31 (each limb in
   [0, 2^31)), so that a limb product plus two limbs fits in OCaml's 63-bit
   [int] ((2^31-1)^2 + 2*(2^31-1) = 2^62 - 1 = max_int).  Normalised: no
   leading (most significant) zero limb, and zero is the unique value
   { sign = 0; mag = [||] }.  Values are immutable; arrays are never shared
   in a way that is later written to.

   Multiplication: schoolbook, Karatsuba above [karatsuba_threshold] limbs.
   Division: one unsigned long division (Knuth, TAOCP vol. 2, 4.3.1,
   Algorithm D), from which the truncated ([tdiv_rem], Rocq's Z.quotrem,
   Zarith's Z.div_rem), Euclidean ([ediv_rem], remainder >= 0, Zarith's
   Z.ediv_rem) and floor ([fdiv_rem], Rocq's Z.div_eucl) pairs are derived.
   Decimal conversions are quadratic (chunks of 9 digits).

   Checked against Zarith on random inputs by tools/bigint_test.ml
   (tools/bigint-test).  The mapping of Rocq's Z onto this module is
   TRUSTED, not proven -- like the Marray mapping. *)

module Bigint = struct

type t = { sign : int; mag : int array }

exception Overflow

let limb_bits = 31
let base = 1 lsl limb_bits
let mask = base - 1

let zero = { sign = 0; mag = [||] }
let one = { sign = 1; mag = [| 1 |] }
let minus_one = { sign = -1; mag = [| 1 |] }

(* ------------------------------------------------------------------ *)
(* Unsigned magnitudes: int arrays, little-endian, base 2^31.          *)
(* Inputs are normalised; outputs are normalised by [trim].           *)
(* ------------------------------------------------------------------ *)

let trim a =
  let n = ref (Array.length a) in
  while !n > 0 && a.(!n - 1) = 0 do decr n done;
  if !n = Array.length a then a else Array.sub a 0 !n

let mk s m = if Array.length m = 0 then zero else { sign = s; mag = m }

let ucmp a b =
  let la = Array.length a and lb = Array.length b in
  if la <> lb then compare la lb
  else begin
    let i = ref (la - 1) in
    while !i >= 0 && a.(!i) = b.(!i) do decr i done;
    if !i < 0 then 0 else compare a.(!i) b.(!i)
  end

let uadd a b =
  let a, b = if Array.length a >= Array.length b then a, b else b, a in
  let la = Array.length a and lb = Array.length b in
  let r = Array.make (la + 1) 0 in
  let carry = ref 0 in
  for i = 0 to la - 1 do
    let s = a.(i) + (if i < lb then b.(i) else 0) + !carry in
    r.(i) <- s land mask;
    carry := s lsr limb_bits
  done;
  r.(la) <- !carry;
  trim r

(* a - b, requires a >= b *)
let usub a b =
  let la = Array.length a and lb = Array.length b in
  let r = Array.make la 0 in
  let borrow = ref 0 in
  for i = 0 to la - 1 do
    let d = a.(i) - (if i < lb then b.(i) else 0) - !borrow in
    if d < 0 then (r.(i) <- d + base; borrow := 1)
    else (r.(i) <- d; borrow := 0)
  done;
  assert (!borrow = 0);
  trim r

(* r[off..] += x, carries propagated; r must be large enough *)
let add_into r off x =
  let carry = ref 0 in
  let lx = Array.length x in
  let i = ref 0 in
  while !i < lx || !carry <> 0 do
    let s = r.(off + !i) + (if !i < lx then x.(!i) else 0) + !carry in
    r.(off + !i) <- s land mask;
    carry := s lsr limb_bits;
    incr i
  done

let umul_school a b =
  let la = Array.length a and lb = Array.length b in
  if la = 0 || lb = 0 then [||]
  else begin
    let r = Array.make (la + lb) 0 in
    for i = 0 to la - 1 do
      let ai = a.(i) in
      if ai <> 0 then begin
        let carry = ref 0 in
        for j = 0 to lb - 1 do
          (* <= (2^31-1)^2 + 2 (2^31-1) = 2^62 - 1 *)
          let t = ai * b.(j) + r.(i + j) + !carry in
          r.(i + j) <- t land mask;
          carry := t lsr limb_bits
        done;
        r.(i + lb) <- !carry
      end
    done;
    trim r
  end

let karatsuba_threshold = 40

(* low n limbs and the rest, both normalised *)
let split a n =
  let la = Array.length a in
  if la <= n then a, [||]
  else trim (Array.sub a 0 n), Array.sub a n (la - n)

let rec umul a b =
  let la = Array.length a and lb = Array.length b in
  if la < karatsuba_threshold || lb < karatsuba_threshold then umul_school a b
  else begin
    let m = (max la lb) / 2 in
    let r = Array.make (la + lb + 1) 0 in
    if lb <= m || la <= m then begin
      (* unbalanced: cut the long operand only *)
      let a, b = if la >= lb then a, b else b, a in
      let a0, a1 = split a m in
      add_into r 0 (umul a0 b);
      add_into r m (umul a1 b)
    end else begin
      let a0, a1 = split a m and b0, b1 = split b m in
      let z0 = umul a0 b0 and z2 = umul a1 b1 in
      let z1 = usub (usub (umul (uadd a0 a1) (uadd b0 b1)) z0) z2 in
      add_into r 0 z0;
      add_into r m z1;
      add_into r (2 * m) z2
    end;
    trim r
  end

(* a * d + c for a small d, c in [0, 2^31) *)
let umul_small_add a d c =
  let la = Array.length a in
  let r = Array.make (la + 1) 0 in
  let carry = ref c in
  for i = 0 to la - 1 do
    let t = a.(i) * d + !carry in
    r.(i) <- t land mask;
    carry := t lsr limb_bits
  done;
  r.(la) <- !carry;
  trim r

(* (a / d, a mod d) for d in (0, 2^31) *)
let udivmod_small a d =
  let la = Array.length a in
  let q = Array.make la 0 in
  let rem = ref 0 in
  for i = la - 1 downto 0 do
    let cur = (!rem lsl limb_bits) lor a.(i) in
    q.(i) <- cur / d;
    rem := cur mod d
  done;
  trim q, !rem

(* number of significant bits of a limb-sized int (0 for 0) *)
let bits_of_int x =
  let n = ref 0 and x = ref x in
  while !x <> 0 do incr n; x := !x lsr 1 done;
  !n

let ushl a n =
  let la = Array.length a in
  if la = 0 || n = 0 then a
  else begin
    let limbs = n / limb_bits and bits = n mod limb_bits in
    let r = Array.make (la + limbs + 1) 0 in
    if bits = 0 then Array.blit a 0 r limbs la
    else begin
      for i = 0 to la - 1 do
        let v = a.(i) lsl bits in
        r.(i + limbs) <- r.(i + limbs) lor (v land mask);
        r.(i + limbs + 1) <- v lsr limb_bits
      done
    end;
    trim r
  end

let ushr a n =
  let la = Array.length a in
  let limbs = n / limb_bits and bits = n mod limb_bits in
  if limbs >= la then [||]
  else begin
    let lr = la - limbs in
    let r = Array.make lr 0 in
    if bits = 0 then Array.blit a limbs r 0 lr
    else
      for i = 0 to lr - 1 do
        let lo = a.(i + limbs) lsr bits in
        let hi = if i + limbs + 1 < la then (a.(i + limbs + 1) lsl (limb_bits - bits)) land mask else 0 in
        r.(i) <- lo lor hi
      done;
    trim r
  end

(* (a / b, a mod b), b <> 0: Knuth's Algorithm D *)
let udivmod a b =
  let la = Array.length a and lb = Array.length b in
  if lb = 0 then raise Division_by_zero
  else if ucmp a b < 0 then [||], a
  else if lb = 1 then begin
    let q, r = udivmod_small a b.(0) in
    q, (if r = 0 then [||] else [| r |])
  end else begin
    (* normalise so that the top limb of v has its bit 30 set *)
    let s = limb_bits - bits_of_int b.(lb - 1) in
    let v = Array.make lb 0 in
    let u = Array.make (la + 1) 0 in
    let shift_into src dst =
      if s = 0 then Array.blit src 0 dst 0 (Array.length src)
      else
        Array.iteri (fun i x ->
          let w = x lsl s in
          dst.(i) <- dst.(i) lor (w land mask);
          dst.(i + 1) <- dst.(i + 1) lor (w lsr limb_bits)) src
    in
    (* v has exactly lb limbs after the shift: use a temporary of lb+1 *)
    let vt = Array.make (lb + 1) 0 in
    shift_into b vt;
    assert (vt.(lb) = 0);
    Array.blit vt 0 v 0 lb;
    shift_into a u;
    let vtop = v.(lb - 1) and vnext = v.(lb - 2) in
    let q = Array.make (la - lb + 1) 0 in
    for j = la - lb downto 0 do
      let num = (u.(j + lb) lsl limb_bits) lor u.(j + lb - 1) in
      let qhat = ref (num / vtop) and rhat = ref (num mod vtop) in
      (* qhat >= base is tested first, so qhat * vnext never overflows *)
      while !rhat < base
            && (!qhat >= base
                || !qhat * vnext > ((!rhat lsl limb_bits) lor u.(j + lb - 2))) do
        decr qhat;
        rhat := !rhat + vtop
      done;
      (* u[j..j+lb] -= qhat * v *)
      let qh = !qhat in
      let carry = ref 0 and borrow = ref 0 in
      for i = 0 to lb - 1 do
        let p = qh * v.(i) + !carry in
        carry := p lsr limb_bits;
        let d = u.(i + j) - (p land mask) - !borrow in
        if d < 0 then (u.(i + j) <- d + base; borrow := 1)
        else (u.(i + j) <- d; borrow := 0)
      done;
      let d = u.(j + lb) - !carry - !borrow in
      if d < 0 then begin
        (* qhat was one too large: add v back *)
        u.(j + lb) <- d land mask;
        q.(j) <- qh - 1;
        let c = ref 0 in
        for i = 0 to lb - 1 do
          let t = u.(i + j) + v.(i) + !c in
          u.(i + j) <- t land mask;
          c := t lsr limb_bits
        done;
        u.(j + lb) <- (u.(j + lb) + !c) land mask
      end else begin
        u.(j + lb) <- d;
        q.(j) <- qh
      end
    done;
    let r = ushr (trim (Array.sub u 0 lb)) s in
    trim q, r
  end

(* ------------------------------------------------------------------ *)
(* Signed integers                                                     *)
(* ------------------------------------------------------------------ *)

let sign x = x.sign
let is_zero x = x.sign = 0

let neg x = if x.sign = 0 then x else { x with sign = - x.sign }
let abs x = if x.sign < 0 then { x with sign = 1 } else x

let compare x y =
  if x.sign <> y.sign then compare x.sign y.sign
  else if x.sign >= 0 then ucmp x.mag y.mag
  else ucmp y.mag x.mag

let equal x y = x.sign = y.sign && ucmp x.mag y.mag = 0
let lt x y = compare x y < 0
let le x y = compare x y <= 0
let gt x y = compare x y > 0
let ge x y = compare x y >= 0
let min x y = if le x y then x else y
let max x y = if ge x y then x else y

let add x y =
  if x.sign = 0 then y
  else if y.sign = 0 then x
  else if x.sign = y.sign then { sign = x.sign; mag = uadd x.mag y.mag }
  else begin
    let c = ucmp x.mag y.mag in
    if c = 0 then zero
    else if c > 0 then mk x.sign (usub x.mag y.mag)
    else mk y.sign (usub y.mag x.mag)
  end

let sub x y = add x (neg y)
let succ x = add x one
let pred x = add x minus_one

let mul x y =
  if x.sign = 0 || y.sign = 0 then zero
  else mk (x.sign * y.sign) (umul x.mag y.mag)

(* -- conversions with OCaml ints -- *)

(* limbs of a 63-bit word read UNSIGNED *)
let limbs_of_word w =
  trim [| w land mask; (w lsr limb_bits) land mask; w lsr (2 * limb_bits) |]

let of_int n =
  if n = 0 then zero
  else if n > 0 then { sign = 1; mag = limbs_of_word n }
  else { sign = -1; mag = limbs_of_word (- n) }  (* -min_int = min_int, read unsigned = 2^62 *)

(* value of the magnitude modulo 2^63, as a 63-bit word *)
let word_of_mag m =
  let l i = if i < Array.length m then m.(i) else 0 in
  l 0 lor (l 1 lsl limb_bits) lor ((l 2 land 1) lsl (2 * limb_bits))

let fits_int x =
  let m = x.mag in
  match Array.length m with
  | 0 | 1 | 2 -> true
  | 3 -> m.(2) = 0 || (x.sign < 0 && m.(2) = 1 && m.(1) = 0 && m.(0) = 0)
  | _ -> false

let to_int x =
  if not (fits_int x) then raise Overflow
  else if x.sign >= 0 then word_of_mag x.mag
  else - (word_of_mag x.mag)

(* [Uint63.t]: a 63-bit word read unsigned by Rocq ([to_Z]).  Two modules
   of that name precede this file, depending on where it is compiled: the
   Kattis shim's (t = int) and rocq-runtime.kernel's in the benchmark
   (abstract, the same int underneath).  Both give [of_int : int -> t] and
   [to_int2 : t -> int * int] (msb, lsb; identities on a 64-bit build), so
   the two crossings below type-check in both settings without an adapter. *)
let of_uint63 (w : Uint63.t) =
  let w = snd (Uint63.to_int2 w) in
  if w = 0 then zero else { sign = 1; mag = limbs_of_word w }

(* reduction modulo 2^63 (Rocq's [Uint63.of_Z]) *)
let to_uint63 x : Uint63.t =
  let w = word_of_mag x.mag in
  Uint63.of_int (if x.sign < 0 then - w else w)

(* -- division -- *)

(* truncated: q rounded toward zero, r has the sign of x (Rocq Z.quotrem,
   Zarith Z.div_rem); raises Division_by_zero *)
let tdiv_rem x y =
  if y.sign = 0 then raise Division_by_zero
  else begin
    let q, r = udivmod x.mag y.mag in
    mk (x.sign * y.sign) q, mk x.sign r
  end

let div_rem = tdiv_rem
let div x y = fst (tdiv_rem x y)
let rem x y = snd (tdiv_rem x y)

(* Euclidean: 0 <= r < |y| (Zarith Z.ediv_rem, Big_int's quomod_big_int) *)
let ediv_rem x y =
  let q, r = tdiv_rem x y in
  if r.sign >= 0 then q, r
  else if y.sign > 0 then pred q, add r y
  else succ q, sub r y

let ediv x y = fst (ediv_rem x y)
let erem x y = snd (ediv_rem x y)

(* floor: q rounded toward -infinity, r has the sign of y (Rocq
   Z.div_eucl / Z.div / Z.modulo for y <> 0) *)
let fdiv_rem x y =
  let q, r = tdiv_rem x y in
  if r.sign <> 0 && r.sign <> y.sign then pred q, add r y else q, r

let fdiv x y = fst (fdiv_rem x y)

(* -- powers, gcd, roots -- *)

let pow x n =
  if n < 0 then invalid_arg "Bigint.pow"
  else begin
    let rec go acc b n =
      if n = 0 then acc
      else go (if n land 1 = 1 then mul acc b else acc)
              (if n > 1 then mul b b else b) (n lsr 1)
    in
    go one x n
  end

let gcd x y =
  let rec go a b = if Array.length b = 0 then a else go b (snd (udivmod a b)) in
  mk 1 (go x.mag y.mag)

(* number of bits of |x| (0 for 0) *)
let numbits x =
  let l = Array.length x.mag in
  if l = 0 then 0 else (l - 1) * limb_bits + bits_of_int x.mag.(l - 1)

(* floor(log2 x) for x > 0 (raises otherwise, like Zarith) *)
let log2 x = if x.sign <= 0 then invalid_arg "Bigint.log2" else numbits x - 1

let shift_left x n =
  if n < 0 then invalid_arg "Bigint.shift_left"
  else mk x.sign (ushl x.mag n)

(* floor sqrt for x >= 0 (raises otherwise, like Zarith) *)
let sqrt x =
  if x.sign < 0 then invalid_arg "Bigint.sqrt"
  else if x.sign = 0 then zero
  else begin
    (* Newton from above: r0 = 2^ceil(numbits/2) >= sqrt x *)
    let rec go r =
      let r' = mk 1 (ushr (uadd r (fst (udivmod x.mag r))) 1) in
      if ucmp r'.mag r < 0 then go r'.mag else r
    in
    mk 1 (go (ushl [| 1 |] ((numbits x + 1) / 2)))
  end

(* -- bits, two's complement semantics on negatives -- *)

let lognot x = pred (neg x)        (* -x - 1 *)

let shift_right x n =
  if n < 0 then invalid_arg "Bigint.shift_right"
  else if x.sign >= 0 then mk 1 (ushr x.mag n)
  else begin
    (* floor: x >> n = lnot ((lnot x) >> n), lnot x >= 0 *)
    let y = lognot x in
    lognot (mk 1 (ushr y.mag n))
  end

let uland a b =
  let n = Stdlib.min (Array.length a) (Array.length b) in
  trim (Array.init n (fun i -> a.(i) land b.(i)))

let ulor a b =
  let n = Stdlib.max (Array.length a) (Array.length b) in
  let g x i = if i < Array.length x then x.(i) else 0 in
  trim (Array.init n (fun i -> g a i lor g b i))

let ulxor a b =
  let n = Stdlib.max (Array.length a) (Array.length b) in
  let g x i = if i < Array.length x then x.(i) else 0 in
  trim (Array.init n (fun i -> g a i lxor g b i))

(* a land (lnot b) *)
let ulandnot a b =
  let g x i = if i < Array.length x then x.(i) else 0 in
  trim (Array.init (Array.length a) (fun i -> a.(i) land (lnot (g b i) land mask)))

let pos m = mk 1 m

let logand x y =
  match x.sign >= 0, y.sign >= 0 with
  | true, true -> pos (uland x.mag y.mag)
  | true, false -> pos (ulandnot x.mag (lognot y).mag)
  | false, true -> pos (ulandnot y.mag (lognot x).mag)
  | false, false -> lognot (pos (ulor (lognot x).mag (lognot y).mag))

let logor x y =
  match x.sign >= 0, y.sign >= 0 with
  | true, true -> pos (ulor x.mag y.mag)
  | true, false -> lognot (pos (ulandnot (lognot y).mag x.mag))
  | false, true -> lognot (pos (ulandnot (lognot x).mag y.mag))
  | false, false -> lognot (pos (uland (lognot x).mag (lognot y).mag))

let logxor x y =
  match x.sign >= 0, y.sign >= 0 with
  | true, true -> pos (ulxor x.mag y.mag)
  | true, false -> lognot (pos (ulxor x.mag (lognot y).mag))
  | false, true -> lognot (pos (ulxor (lognot x).mag y.mag))
  | false, false -> pos (ulxor (lognot x).mag (lognot y).mag)

let utestbit m n =
  let i = n / limb_bits in
  i < Array.length m && (m.(i) lsr (n mod limb_bits)) land 1 = 1

let testbit x n =
  if n < 0 then invalid_arg "Bigint.testbit"
  else if x.sign >= 0 then utestbit x.mag n
  else not (utestbit (lognot x).mag n)

(* -- decimal strings -- *)

let chunk = 1_000_000_000   (* 10^9 < 2^31 *)

let to_string x =
  if x.sign = 0 then "0"
  else begin
    let parts = ref [] and m = ref x.mag in
    while Array.length !m > 0 do
      let q, r = udivmod_small !m chunk in
      parts := r :: !parts;
      m := q
    done;
    let b = Buffer.create (10 * List.length !parts + 1) in
    if x.sign < 0 then Buffer.add_char b '-';
    (match !parts with
     | [] -> ()
     | p :: rest ->
       Buffer.add_string b (string_of_int p);
       List.iter (fun p -> Buffer.add_string b (Printf.sprintf "%09d" p)) rest);
    Buffer.contents b
  end

(* optional leading '-' or '+', then at least one decimal digit *)
let of_string s =
  let n = String.length s in
  let neg_, start =
    if n > 0 && s.[0] = '-' then true, 1
    else if n > 0 && s.[0] = '+' then false, 1
    else false, 0 in
  if start >= n then invalid_arg "Bigint.of_string";
  let m = ref [||] in
  let i = ref start in
  while !i < n do
    let len = Stdlib.min 9 (n - !i) in
    let v = ref 0 and p = ref 1 in
    for k = !i to !i + len - 1 do
      let c = s.[k] in
      if c < '0' || c > '9' then invalid_arg "Bigint.of_string";
      v := !v * 10 + (Char.code c - 48);
      p := !p * 10
    done;
    m := umul_small_add !m !p !v;
    i := !i + len
  done;
  mk (if neg_ then -1 else 1) !m

end


(* Expose the embedded module as the separately compiled Bigint module,
   matching the legacy arrays_bigint build without changing its arithmetic. *)
include Bigint
