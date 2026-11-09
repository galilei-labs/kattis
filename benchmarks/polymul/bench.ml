(* Benchmark the unmodified extracted functions with the same Marray runtime. *)
let schoolbook = Polymul1_extracted_marray.polymul
let fft = Polymul2_extracted_marray.polymul
let sink = ref (Marray.of_array [||] Uint63.zero)
let seed = 20261109
let trials = 7
let sizes = [16;32;64;128;192;256;384;512;768;1024;1536;2048;3072;4096;6144;8192;12288;16384]

let inputs n trial =
  let rng = Random.State.make [|seed; n; trial|] in
  let input () =
    let a = Array.init n (fun _ -> Random.State.int rng 7 - 3) in
    (* Ensure that the degree really is n-1. *)
    if a.(n-1) = 0 then a.(n-1) <- 1;
    a, Marray.of_array (Array.map Uint63.of_int a) Uint63.zero
  in
  input (), input ()

let verify n ai bi a b =
  let before_a = Array.copy a.Marray.data in
  let before_b = Array.copy b.Marray.data in
  let expected = schoolbook a b in
  let actual = fft a b in
  if Array.length actual.Marray.data <> 2*n-1 then failwith "Incorrect result length";
  Array.iteri (fun i x ->
    if not (Uint63.equal x actual.Marray.data.(i)) then
      failwith (Printf.sprintf "Output mismatch at size %d, coefficient %d" n i)) expected.Marray.data;
  if n <= 256 then begin
    let reference = Array.make (2*n-1) 0 in
    Array.iteri (fun i x -> Array.iteri (fun j y -> reference.(i+j) <- reference.(i+j)+x*y) bi) ai;
    Array.iteri (fun i x -> if not (Uint63.equal (Uint63.of_int x) actual.Marray.data.(i))
      then failwith "Mismatch with independent integer convolution") reference
  end;
  if before_a <> a.Marray.data || before_b <> b.Marray.data then failwith "An input was mutated"

let timed f a b reps =
  Gc.full_major ();
  let start = Unix.gettimeofday () in
  for _ = 1 to reps do sink := Sys.opaque_identity (f a b) done;
  (Unix.gettimeofday () -. start) /. float_of_int reps

let repetitions f a b =
  let rec calibrate reps =
    let per_call = timed f a b reps in
    if per_call *. float_of_int reps >= 0.03 || reps >= 4096 then reps
    else calibrate (min 4096 (max (reps+1) (min (reps*8) (int_of_float (0.04 /. max per_call 1e-9)))))
  in calibrate 1

let () =
  let csv = open_out Sys.argv.(1) in
  output_string csv "coefficients_per_input,total_coefficients,degree_per_input,trial,algorithm,repetitions,seconds_per_call\n";
  List.iter (fun n ->
    let (_,a0),(_,b0) = inputs n 0 in
    let school_reps = repetitions schoolbook a0 b0 in
    let fft_reps = repetitions fft a0 b0 in
    for trial = 0 to trials-1 do
      let (ai,a),(bi,b) = inputs n trial in
      verify n ai bi a b;
      let run name f reps =
        let elapsed = timed f a b reps in
        Printf.fprintf csv "%d,%d,%d,%d,%s,%d,%.12g\n" n (2*n) (n-1) trial name reps elapsed;
        flush csv
      in
      if trial mod 2 = 0 then (run "schoolbook" schoolbook school_reps; run "fft" fft fft_reps)
      else (run "fft" fft fft_reps; run "schoolbook" schoolbook school_reps)
    done;
    Printf.printf "%d coefficients per input: 7 matching outputs and timing trials complete\n%!" n
  ) sizes;
  close_out csv
