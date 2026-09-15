(*
 * RunNet -- run a GeneralCaracaraProgram concretely and print what it did.
 *
 * This is the EXTRACTED evaluator, exposed as a tool.  It exists so that a
 * test outside this repository can use the real semantics as its oracle
 * instead of reimplementing them: ~/proj/ect's property tests compare a
 * lowered program's return value against a BPF interpreter, and the IR side of
 * that comparison has to be the evaluator the Coq development is actually
 * about, not a second model that could be wrong in the same places the
 * translator is.
 *
 * Two modes:
 *
 *   run_net <prog.ir> [<region>:<offset>:<width>:<value> ...]
 *       one run, printed to stdout.
 *
 *   run_net --serve
 *       a co-process: one command per line on stdin, a reply terminated by a
 *       line containing only ".".  Starting the process costs far more than a
 *       run, and a property test needs hundreds, so this is the mode the
 *       harness uses.
 *
 *         run <prog.ir> [<region>:<offset>:<width>:<value> ...]
 *         forget <prog.ir>      -- drop it from the cache, for a caller that
 *                                  rewrites the same temporary path
 *         quit
 *
 * `pkt:<hex>` seeds the INPUT PACKET, as hex bytes.  Without it the read tape
 * is empty, so any program whose parser extracts anything rejects -- right for
 * a program whose input is memory (an eBPF one), useless for a P4 one.
 *
 * A seed writes `value` at `offset` of `region` at `width` BITS (8/16/32/64),
 * little-endian across the bytes it covers -- the same thing
 * Shim.set_net_mem_cell does.
 *
 * The reply is the emitted packet, then every declared region's final contents
 * and access extent.  A run that rejects replies with only "reject", which is
 * the whole observable: two runs that both reject are indistinguishable,
 * exactly as modnet_equivalence_checker treats them.
 *)

(* "0a0b0c" -> [10; 11; 12].  A packet is given as hex bytes because that is how
   everything else writes one down; an odd digit count is an error rather than a
   guess about which nibble was meant. *)
let bytes_of_hex (h : string) : int Stdlib.List.t =
  let n = Stdlib.String.length h in
  if n mod 2 <> 0 then failwith "pkt: needs an even number of hex digits";
  let rec go i acc =
    if i >= n then Stdlib.List.rev acc
    else
      let b = int_of_string ("0x" ^ Stdlib.String.sub h i 2) in
      go (i + 2) (b :: acc) in
  go 0 []

let width_of = function
  | "8"  -> CrVal.W8
  | "16" -> CrVal.W16
  | "32" -> CrVal.W32
  | _    -> CrVal.W64

(* The declarations come back as an extracted Coq list, not an OCaml one. *)
let rec of_coq_list = function
  | Datatypes.Coq_nil -> []
  | Datatypes.Coq_cons (x, rest) -> x :: of_coq_list rest

let region_ids p =
  Stdlib.List.map
    (fun d ->
       Shim.coq_Z_to_int
         (BinNums.Zpos
            (CrIdentifiers.coq_Posesque_MemRegion.unwrap d.CrModule.mr_id)))
    (of_coq_list (CrModule.get_mem_regions_from_general p))

let split_ws s =
  Stdlib.List.filter (fun x -> x <> "") (Stdlib.String.split_on_char ' ' s)

let run_with (p : CrModule.coq_GeneralCaracaraProgram) seeds =
  let gcs0 = CrVarLike.init_general_concrete_state p in
  let gcs =
    Stdlib.List.fold_left
      (fun g spec ->
         match Stdlib.String.split_on_char ':' spec with
         | ["pkt"; hex] -> Shim.set_net_packet (bytes_of_hex hex) g
         | [r; off; w; v] ->
             Shim.set_net_mem_cell (int_of_string r) (int_of_string off)
               (width_of w) (int_of_string v) g
         | _ -> g)
      gcs0 seeds in
  (match CrConcreteSemanticsModule.eval_general_program_concrete p gcs with
   | None -> print_endline "reject(None)"
   | Some s ->
       (match s.CrGeneralProgramState.gps_valid with
        | Datatypes.Coq_false -> print_endline "reject"
        | Datatypes.Coq_true ->
            Shim.print_net_output s;
            Stdlib.List.iter
              (fun r ->
                 Shim.print_net_mem_region r s;
                 Shim.print_net_mem_extent r s)
              (region_ids p)))

let run_once path seeds =
  run_with (Shim.load_general_program path) seeds

let serve () =
  (* Loading and sexp-parsing a program is far more expensive than running it,
     and a mutation sweep runs the same pair hundreds of times. *)
  let cache = Hashtbl.create 8 in
  let load_cached path =
    match Hashtbl.find_opt cache path with
    | Some p -> p
    | None ->
        let p = Shim.load_general_program path in
        Hashtbl.add cache path p; p in
  let reply () = print_endline "."; flush Stdlib.stdout in
  (try
     while true do
       match split_ws (input_line Stdlib.stdin) with
       | [] -> ()
       | ["quit"] -> raise Exit
       | ["forget"; path] -> Hashtbl.remove cache path; reply ()
       | "run" :: path :: seeds ->
           run_with (load_cached path) seeds;
           reply ()
       | _ -> print_endline "?"; reply ()
     done
   with End_of_file | Exit -> ())



let usage () =
  prerr_endline "usage: run_net <prog.ir> [pkt:<hex>] [<region>:<offset>:<width>:<value> ...]";
  prerr_endline "       run_net --serve";
  prerr_endline "  Runs a GeneralCaracaraProgram concretely and prints the";
  prerr_endline "  emitted packet, then each region's contents and extent.";
  prerr_endline "  --serve reads commands from stdin; see the top of RunNet.ml.";
  exit 1

let () =
  match Stdlib.List.tl (Array.to_list Sys.argv) with
  | ["--serve"] -> serve ()
  | path :: seeds when Stdlib.String.length path > 0
                       && Stdlib.String.get path 0 <> '-' ->
      run_once path seeds
  | _ -> usage ()
