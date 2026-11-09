(* Large-size extension with validation outside the timed multiplication. *)
let multiply = if Sys.argv.(3) = "schoolbook" then Polymul1_extracted_marray.polymul else Polymul2_extracted_marray.polymul
let seed = 20261109
let inputs n trial =
  let rng = Random.State.make [|seed; n; trial|] in
  let input () =
    let a = Array.init n (fun _ -> Random.State.int rng 7 - 3) in
    if a.(n-1) = 0 then a.(n-1) <- 1;
    a, Marray.of_array (Array.map Uint63.of_int a) Uint63.zero
  in input (),input ()

let validate n trial ai bi a b result =
  if Array.length result.Marray.data <> 2*n-1 then failwith "Incorrect length";
  let c = Array.map (fun x -> Int64.to_int (Uint63.to_int64 x)) result.Marray.data in
  Array.iteri (fun i x ->
    if x <> Int64.to_int (Uint63.to_int64 a.Marray.data.(i)) ||
       bi.(i) <> Int64.to_int (Uint63.to_int64 b.Marray.data.(i)) then failwith "Input mutated") ai;
  Array.iter (fun x -> if abs x > 9*n then failwith "Coefficient exceeds elementary product bound") c;
  let rng = Random.State.make [|seed; n; trial; 99|] in
  let indices = [0; n-1; 2*n-2] @ List.init 32 (fun _ -> Random.State.int rng (2*n-1)) in
  List.iter (fun k ->
    let expected = ref 0 in
    for i = max 0 (k-n+1) to min (n-1) k do expected := !expected + ai.(i)*bi.(k-i) done;
    if c.(k) <> !expected then failwith (Printf.sprintf "Convolution mismatch at %d" k)) indices;
  (* Products of residues <1e9+9 fit within a 63-bit OCaml int. *)
  List.iter (fun prime ->
    let norm x = let r=x mod prime in if r < 0 then r+prime else r in
    let eval coeffs x =
      let r = ref 0 in
      for i=Array.length coeffs-1 downto 0 do r := norm (!r*x+coeffs.(i)) done; !r in
    for _=1 to 2 do
      let x=1+Random.State.int rng (prime-1) in
      if eval c x <> (eval ai x * eval bi x) mod prime then failwith "Polynomial identity mismatch"
    done) [1_000_000_007;1_000_000_009]

let () =
  let n = int_of_string Sys.argv.(1) in
  if n < 2 || n > 131072 then invalid_arg "Outside Kattis degree bounds";
  let csv = open_out Sys.argv.(2) in
  let (_,a),(_,b) = inputs n 999 in
  ignore (Sys.opaque_identity (multiply a b));
  for trial=0 to 6 do
    let (ai,a),(bi,b) = inputs n trial in
    Gc.full_major ();
    let start = Unix.gettimeofday () in
    let result = Sys.opaque_identity (multiply a b) in
    let elapsed = Unix.gettimeofday () -. start in
    validate n trial ai bi a b result;
    Printf.fprintf csv "%d,%d,%d,%d,%s,1,%.12g\n" n (2*n) (n-1) trial Sys.argv.(3) elapsed;
    flush csv
  done;
  close_out csv
