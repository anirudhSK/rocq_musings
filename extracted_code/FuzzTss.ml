(* fuzz_tss -- run the linear_db/tss_db equivalence check over randomly
   generated filter databases.

   The expect tests in TestEquality.ml run a small fixed-seed campaign so CI
   stays fast; this is the same generator with the knobs exposed, for running a
   campaign big enough to actually find something.  Generation, the failure
   report and both probes live in [PktClassFuzz] so the two cannot drift.

     fuzz_tss [--seed N] [--count N] [--size N[,N...]] [--mutate|--prec] [-v]

   --size takes the filter counts to cycle through (default 1,2,3,4).  Exits
   non-zero if any database came back other than Equivalent; a failure prints
   the database and the one-database seed that reproduces it.

   --mutate inverts the expectation: it relabels the tss side, so every
   database whose classification is observable at all must come back
   NotEquivalent.  That is the control for a suite of Equivalent verdicts,
   which on its own is also what two programs that both emit zeros produce.

   --prec is the coverage number rather than a verdict: it inverts the
   priorities on the tss side and reports how many databases NOTICED, i.e. how
   many have a packet matching two filters with different labels.  Those are
   the ones where the campaign is comparing the two arbitration schemes and not
   just two ways of matching a single filter. *)

let usage () =
  prerr_endline
    "usage: fuzz_tss [--seed N] [--count N] [--size N[,N...]] \
     [--mutate|--prec] [-v]";
  exit 2

let () =
  let seed = ref 1 and count = ref 20 and verbose = ref false in
  let mutate = ref false and prec = ref false in
  let sizes = ref [| 1; 2; 3; 4 |] in
  let args = Stdlib.Array.to_list Sys.argv in
  let rec parse = function
    | [] -> ()
    | "--seed" :: v :: rest -> seed := int_of_string v; parse rest
    | "--count" :: v :: rest -> count := int_of_string v; parse rest
    | "--size" :: v :: rest ->
      sizes := Stdlib.Array.of_list
                 (Stdlib.List.map int_of_string
                    (Stdlib.String.split_on_char ',' v));
      parse rest
    | "--mutate" :: rest -> mutate := true; parse rest
    | "--prec" :: rest -> prec := true; parse rest
    | ("-v" | "--verbose") :: rest -> verbose := true; parse rest
    | _ -> usage () in
  parse (Stdlib.List.tl args);
  if !count <= 0 || Stdlib.Array.length !sizes = 0 then usage ();
  if Stdlib.Array.exists (fun n -> n < 0) !sizes then usage ();
  if !mutate && !prec then usage ();
  let sizes_str =
    Stdlib.String.concat ";"
      (Stdlib.Array.to_list (Stdlib.Array.map string_of_int !sizes)) in
  if !prec then begin
    Printf.printf
      "fuzz_tss: %d databases, seed %d, sizes [%s], precedence probe\n%!"
      !count !seed sizes_str;
    let flipped =
      PktClassFuzz.run_precedence_probe ~seed:!seed ~count:!count
        ~sizes:!sizes () in
    Printf.printf "%d/%d databases exercise precedence\n" flipped !count;
    (* A coverage number: nothing here is a failure, but a campaign in which
       NOTHING exercises precedence is only testing half the claim. *)
    exit (if flipped = 0 then 1 else 0)
  end else begin
    Printf.printf "fuzz_tss: %d databases, seed %d, sizes [%s]%s\n%!"
      !count !seed sizes_str
      (if !mutate then ", relabelled (expecting NotEquivalent)" else "");
    let failures =
      PktClassFuzz.run_campaign ~verbose:!verbose ~mutate:!mutate ~seed:!seed
        ~count:!count ~sizes:!sizes () in
    if failures = 0 then
      Printf.printf "%d/%d as expected (%s)\n" !count !count
        (if !mutate then "NotEquivalent" else "Equivalent")
    else
      Printf.printf "%d/%d databases came back wrong\n" failures !count;
    exit (if failures = 0 then 0 else 1)
  end
