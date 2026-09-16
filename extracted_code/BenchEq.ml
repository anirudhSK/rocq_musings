(* bench_eq -- time equivalence-check queries, reproducibly.

   One place that says what the evaluation checks and how big each case is, so
   a table in the paper is generated rather than transcribed.

     dune exec bench_eq -- [--family F] [--case SUBSTR] [--reps N]
                           [--csv FILE] [--list] [--timeout S]

   What is timed is the CHECK ONLY: building the two programs (reading and
   parsing an s-expression, or generating a TSS pair in Rocq) happens once,
   before the clock starts, and is reported separately as [build_ms].  The
   checker is then run [--reps] times on those same two in-memory programs and
   the MEDIAN is reported, with min and max alongside, because Z3's time on one
   query varies run to run.  Reps default to 3; use 1 for a quick sweep and
   more when a number is going into a table.

   Every case carries the verdict it is supposed to produce.  A case that
   reports the wrong verdict is marked BAD and exits non-zero: a timing for a
   query that answered the wrong question is not a timing worth quoting, and
   an Equivalent suite with no NotEquivalent controls is exactly what two
   programs that both do nothing would produce.

   Sizes come from [IrSize], which walks the same in-memory program that was
   handed to the checker. *)

(* ------------------------------------------------------------------ *)
(* A case supplies its two programs on demand.  The three shapes match how the
   evaluation actually gets a program: from a pair of .ir files, from a pair of
   single-transformer s-expressions, or generated in Rocq. *)

type pair =
  | Net  of Stdlib.String.t * Stdlib.String.t
    (* two GeneralCaracaraProgram s-expressions, by path from the repository
       root.  Every P4, eBPF and ParserHawk row is one of these, reading a
       CHECKED-IN artifact under bench/: the point of the benchmark is the
       cost of the CHECK, so compiling P4 with p4c or C with clang happens
       once, out of band, and bench/<family>/regen.sh is what does it.  See
       bench/README.md. *)
  | GenNet of Stdlib.String.t
      * (unit -> CrModule.coq_GeneralCaracaraProgram
                 * CrModule.coq_GeneralCaracaraProgram)
    (* built in Rocq; the string says how, for the --list output.  The TSS
       pairs are generated rather than stored because a database is a Rocq
       value and a seed reproduces it exactly, and the ParserHawk pairs
       because one side of each is a SPEC that lives in ParserHawkEval.v and
       has no file form. *)

type verdict = Eq | NotEq | NotEqUnknown | NotEqVarsDiffer

type case = {
  family : Stdlib.String.t;   (* TSS | P4 | eBPF | ParserHawk | Core *)
  name   : Stdlib.String.t;
  what   : Stdlib.String.t;   (* what the pair is, for --list and the paper *)
  pair   : pair;
  want   : verdict;
}

let verdict_str = function
  | Eq -> "Equivalent"
  | NotEq -> "NotEquivalent"
  | NotEqUnknown -> "NotEquivalentUnknown"
  | NotEqVarsDiffer -> "NotEquivalentVariablesDiffer"

let of_smt = function
  | SmtQuery.Equivalent -> Eq
  | SmtQuery.NotEquivalent _ -> NotEq
  | SmtQuery.NotEquivalentUnknown -> NotEqUnknown
  | SmtQuery.NotEquivalentVariablesDiffer -> NotEqVarsDiffer

(* ------------------------------------------------------------------ *)
(* Paths are relative to the repository root, which is two levels up from the
   build directory the executable runs in.  [root] makes a case's path
   independent of where bench_eq was invoked from. *)

let root =
  (* Walk up from a starting point until a directory holding the repository's
     marker files is found.  Counting levels instead would depend on where the
     executable happens to sit, which differs between [dune exec] and running
     _build/default/... directly. *)
  let is_root d =
    Sys.file_exists (Filename.concat d "dune-project")
    && Sys.file_exists (Filename.concat d "extracted_code")
  in
  let rec search d =
    if is_root d then Some d
    else
      let up = Filename.dirname d in
      if up = d then None else search up
  in
  match Sys.getenv_opt "CARACARA_ROOT" with
  | Some r -> r
  | None ->
    match search (Sys.getcwd ()) with
    | Some r -> r
    | None ->
      match search (Filename.dirname Sys.executable_name) with
      | Some r -> r
      | None ->
        prerr_endline
          "bench_eq: cannot locate the repository root; set CARACARA_ROOT";
        exit 2

let path p = if Filename.is_relative p then Filename.concat root p else p

(* ------------------------------------------------------------------ *)
(* The registry.  Adding an evaluation program means adding a line here. *)

let gp f = Shim.load_general_program (path f)

(* A ParserHawk artifact is a bare [Parser] record, not a network: the tool
   emits a pipeline, and [ParserHawkEval.dump_headers] is what wraps one into
   the parser+deparser network the checker compares.  Which headers to dump is
   part of the benchmark, since it is what "the same program" means for two
   pipelines that name their headers differently. *)
let ph f hdrs =
  let x = open_in (path f) in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  let p = str |> Sexplib.Sexp.of_string |> CrTypeIF.CrParser.coq_Parser_of_sexp in
  ParserHawkEval.dump_headers p hdrs

(* One sample from the fuzz generator, as a (linear, tss) pair.  Taking the
   seed and the filter count makes the row reproducible: the same two numbers
   give the same database on any machine, because PktClassFuzz carries its own
   splitmix64 rather than using Random. *)
let tss_gen seed nfilters =
  let r = PktClassFuzz.rng_make seed in
  let db, _doc = PktClassFuzz.random_db r nfilters in
  PktClass.linear_db db, PktClass.tss_db db

let h = Shim.int_to_pos
let icmp_hdrs = ParserHawkEval.ICMPHdr (h 1, h 2)
let eth_hdrs  = ParserHawkEval.EthHdr (h 1, h 2)
let mfk_hdrs  = ParserHawkEval.MultiFieldHdr (h 1, h 2, h 3)
let sai_hdrs  =
  ParserHawkEval.SAIHdr (h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9)

let cases : case list = [

  (* ---------------- TSS: the packet-classifier case study ------------- *)
  (* [linear_db] is the specification -- a linear scan that tracks the highest
     priority seen -- and [tss_db] is tuple space search over the same
     database, a per-table best joined by a strictly-lower-wins merger.  The
     two constructions have nothing structurally in common, so the claim that
     they classify every 192-bit packet alike is the real content of these
     rows.  The generated databases carry the seed and the filter count,
     because PktClassFuzz has its own splitmix64 rather than using [Random]
     and so reproduces exactly on any machine. *)

  { family = "TSS"; name = "simple";
    what = "spec vs tuple space search, SimpleDB (3 hand-written filters)";
    pair = GenNet ("PktClass.ex_lin_prog / ex_tss_prog",
                   fun () -> PktClass.ex_lin_prog, PktClass.ex_tss_prog);
    want = Eq };

  { family = "TSS"; name = "gen-2";
    what = "spec vs tuple space search, generated database of 2 filters (seed 1)";
    pair = GenNet ("PktClassFuzz.random_db 2",
                   fun () -> tss_gen 1 2); want = Eq };

  { family = "TSS"; name = "gen-8";
    what = "spec vs tuple space search, generated database of 8 filters (seed 1)";
    pair = GenNet ("PktClassFuzz.random_db 8",
                   fun () -> tss_gen 1 8); want = Eq };

  (* The control for the three above, and it is not decoration.  Every TSS row
     is Equivalent, and a suite of those alone is also what a checker that had
     stopped observing anything would produce -- or what two databases that
     classify NOTHING would produce, which is the failure mode the fuzz
     generator's witness packets exist to avoid (see CLAUDE.md).  Two tss
     pipelines over DIFFERENT databases must be separated. *)
  { family = "TSS"; name = "cross-8";
    what = "two tuple-space pipelines over different 8-filter databases (control)";
    pair = GenNet ("PktClassFuzz.random_db 8, seeds 1 and 2",
                   fun () -> snd (tss_gen 1 8), snd (tss_gen 2 8));
    want = NotEq };

  (* ---------------- P4: one program, before and after p4c's midend ---- *)
  (* Every P4 row is ONE source compiled twice by the SAME p4c: once as the
     rocq extension sees it straight from the frontend, and once after the
     midend has rewritten it.  That is a statement about p4c's own optimizer
     rather than about two spellings a person wrote, and it needs no second
     compiler and no historic checkout -- `p4test --top4 MidEnd --dump DIR`
     writes the program after each midend pass as ordinary P4 source.

     The .ir files are generated by bench/p4/regen.sh, which records the exact
     flags; bench/p4/README.md says what each pair is and why two passes are
     excluded from ConQuest. *)

  { family = "P4"; name = "basic";
    what = "p4lang/tutorials basic.p4, frontend vs the whole midend";
    pair = Net ("bench/p4/ir/basic_src.ir", "bench/p4/ir/basic_midend.ir");
    want = Eq };

  { family = "P4"; name = "basic-tunnel";
    what = "p4lang/tutorials basic_tunnel.p4, frontend vs the whole midend";
    pair = Net ("bench/p4/ir/basic_tunnel_src.ir",
                "bench/p4/ir/basic_tunnel_midend.ir");
    want = Eq };

  (* multicast is the one program the midend is INVISIBLE to: its lowered IR
     is byte-identical before and after, and excluding any single midend pass
     leaves it byte-identical too.  The passes that do change multicast's
     dumped P4 text -- EliminateTypedefs and P4::FlattenHeaderUnion -- change
     nothing the lowering can see.  The row is kept because it still solves a
     universally quantified query, and because "the whole midend changes
     nothing here" is the finding. *)
  { family = "P4"; name = "multicast";
    what = "p4lang/tutorials multicast.p4, frontend vs the whole midend \
            (the lowered IR is byte-identical; no midend pass changes it)";
    pair = Net ("bench/p4/ir/multicast_src.ir",
                "bench/p4/ir/multicast_midend.ir");
    want = Eq };

  { family = "P4"; name = "qos";
    what = "p4lang/tutorials qos.p4, frontend vs the whole midend";
    pair = Net ("bench/p4/ir/qos_src.ir", "bench/p4/ir/qos_midend.ir");
    want = Eq };

  (* Princeton-Cabernet ConQuest's baseline forwarding program, used
     unmodified -- a Tofino-native program.  EliminateTuples is excluded from
     the midend side and the reason is a limitation of the LOWERING, not of
     p4c: it declares a `tuple_0` struct ahead of the header struct, which
     shifts every later header uid, and the checker gives the two programs ONE
     free register per uid.  With it included the pair reports NotEquivalent
     on a uid mismatch rather than a behavioural difference.  HandleNoMatch is
     excluded because it puts `verify(false, error.NoMatch)` into the parser,
     which the parser lowering does not accept.  Both are recorded in
     bench/p4/README.md. *)
  { family = "P4"; name = "conquest";
    what = "Princeton-Cabernet ConQuest baseline, frontend vs the midend \
            with EliminateTuples excluded";
    pair = Net ("bench/p4/ir/conquest_src.ir", "bench/p4/ir/conquest_midend.ir");
    want = Eq };

  (* A REAL p4c MISCOMPILATION, not a seeded one.  p4lang/p4c issue #5765:
     GlobalCopyPropagation keeps a stale constant across an out argument,
     because it drops variables matching the CALLEE's formal parameter name
     rather than the actual argument, so an action reading a variable that
     random() has just written is rewritten to the old constant.

     It is the one P4 row whose expected verdict is a DEFECT rather than a
     control: if it ever reports Equivalent, the p4c in translation/p4c has
     been updated with the fix.  Confirm against the issue and retire the row
     rather than "fixing" it. *)
  { family = "P4"; name = "issue5765";
    what = "p4c #5765: one source with and without GlobalCopyPropagation";
    pair = Net ("bench/p4/ir/issue5765_gcp.ir", "bench/p4/ir/issue5765_nogcp.ir");
    want = NotEq };

  (* ---------------- eBPF: one C source at two optimization levels ----- *)
  (* The same shape as the P4 rows and for the same reason: each pair is one
     program against the SAME program after LLVM's optimizer has had at it,
     which is a statement about the optimizer rather than about two things
     somebody wrote.  bench/ebpf/regen.sh builds them; bench/ebpf/README.md
     says why four of the five are -O1 against -O2. *)

  { family = "eBPF"; name = "xdp-pktcntr";
    what = "dslab-epfl/ebpf-se katran/xdp_pktcntr.c, -O1 vs -O2";
    pair = Net ("bench/ebpf/ir/xdp_pktcntr_O1.ir",
                "bench/ebpf/ir/xdp_pktcntr_O2.ir");
    want = Eq };

  { family = "eBPF"; name = "cls-pktcntr";
    what = "dslab-epfl/ebpf-se katran/adapter_integration_test_kern.c, -O1 vs -O2";
    pair = Net ("bench/ebpf/ir/cls_pktcntr_O1.ir",
                "bench/ebpf/ir/cls_pktcntr_O2.ir");
    want = Eq };

  { family = "eBPF"; name = "map-access";
    what = "dslab-epfl/ebpf-se fw/xdp_map_access_kern.c, -O1 vs -O2";
    pair = Net ("bench/ebpf/ir/map_access_O1.ir",
                "bench/ebpf/ir/map_access_O2.ir");
    want = Eq };

  { family = "eBPF"; name = "suricata-filter";
    what = "OISF/suricata filter.c, -O1 vs -O2";
    pair = Net ("bench/ebpf/ir/filter_O1.ir", "bench/ebpf/ir/filter_O2.ir");
    want = Eq };

  (* A -O0 against -O2 pair. *)
  { family = "eBPF"; name = "suricata-vlan";
    what = "OISF/suricata vlan_filter.c, -O0 vs -O2";
    pair = Net ("bench/ebpf/ir/vlan_filter_O0.ir",
                "bench/ebpf/ir/vlan_filter_O2.ir");
    want = Eq };

  (* ---------------- ParserHawk: synthesized parser pipelines ---------- *)
  (* ParserHawk synthesizes a hardware parser pipeline from a spec.  Two
     questions are asked of it: does a synthesized pipeline agree with the
     spec it came from, and do the pipelines for two different targets agree
     with each other.  The spec side is a Rocq value in ParserHawkEval.v --
     it has no file form -- and [dump_headers] wraps a pipeline into the
     parser+deparser network that makes two of them comparable.

     bench/parserhawk/ holds the pipeline JSON and the .ir lowered from it;
     regenerating a .json means re-running ParserHawk's CEGIS loop, which is a
     synthesis search, so the JSON is an input artifact here. *)

  (* start_ethernet, all three ways round.  Its spec selects on a mask whose
     bits are NOT contiguous (0xfa00 is bits 15..11 and bit 9), which a
     SelectCase cannot express in one arm -- so the two pipelines each chain
     two select states to say it, while eth_spec says it as the two values the
     one contiguous slice can take.  Three different spellings of one
     condition, which is what makes the cross pair worth having on top of the
     two spec pairs. *)
  { family = "ParserHawk"; name = "ethernet-tofino";
    what = "start_ethernet: the synthesized Tofino pipeline vs its spec";
    pair = GenNet ("ethernet_tofino.ir / eth_spec",
                   fun () -> ph "bench/parserhawk/ir/ethernet_tofino.ir" eth_hdrs,
                             ParserHawkEval.eth_spec);
    want = Eq };

  { family = "ParserHawk"; name = "ethernet-ipu";
    what = "start_ethernet: the synthesized IPU pipeline vs its spec";
    pair = GenNet ("ethernet_ipu.ir / eth_spec",
                   fun () -> ph "bench/parserhawk/ir/ethernet_ipu.ir" eth_hdrs,
                             ParserHawkEval.eth_spec);
    want = Eq };

  { family = "ParserHawk"; name = "ethernet-cross";
    what = "start_ethernet: the Tofino pipeline against the IPU one";
    pair = GenNet ("ethernet_tofino.ir / ethernet_ipu.ir",
                   fun () -> ph "bench/parserhawk/ir/ethernet_tofino.ir" eth_hdrs,
                             ph "bench/parserhawk/ir/ethernet_ipu.ir" eth_hdrs);
    want = Eq };

  { family = "ParserHawk"; name = "icmp-ipu";
    what = "Parse icmp: the synthesized IPU pipeline vs its spec";
    pair = GenNet ("icmp_ipu.ir / icmp_spec",
                   fun () -> ph "bench/parserhawk/ir/icmp_ipu.ir" icmp_hdrs,
                             ParserHawkEval.icmp_spec);
    want = Eq };

  { family = "ParserHawk"; name = "multifield-tofino";
    what = "Multi-keys: the synthesized Tofino pipeline vs its spec";
    pair = GenNet ("multifield_tofino.ir / mfk_spec",
                   fun () -> ph "bench/parserhawk/ir/multifield_tofino.ir" mfk_hdrs,
                             ParserHawkEval.mfk_spec);
    want = Eq };

  (* The bug, and the row is the finding rather than a failure.  The IPU
     pipeline for Multi-keys does NOT agree with its spec: ParserHawk's Z3
     model was right and its JSON writer dropped a lower-bound check on a
     node's transition rules, so the emitted pipeline carries transition edges
     the model never had.  A run where this comes back Equivalent means the
     artifact has been regenerated. *)
  { family = "ParserHawk"; name = "multifield-ipu";
    what = "Multi-keys: the synthesized IPU pipeline vs its spec (the ParserHawk bug)";
    pair = GenNet ("multifield_ipu.ir / mfk_spec",
                   fun () -> ph "bench/parserhawk/ir/multifield_ipu.ir" mfk_hdrs,
                             ParserHawkEval.mfk_spec);
    want = NotEq };

  (* SAI v4, not v2: both the spec in ParserHawkEval.v and the pipeline JSON
     come from ParserHawk's sai_v4_pkt_eth_v46_inv4_udp_tcp_icmp_arp example.
     The largest pipeline here, nine extracted fields. *)
  { family = "ParserHawk"; name = "sai-tofino";
    what = "SAI v4: the synthesized Tofino pipeline vs its spec";
    pair = GenNet ("sai_tofino.ir / sai_spec",
                   fun () -> ph "bench/parserhawk/ir/sai_tofino.ir" sai_hdrs,
                             ParserHawkEval.sai_spec);
    want = Eq };

  { family = "ParserHawk"; name = "sai-ipu";
    what = "SAI v4: the synthesized IPU pipeline vs its spec";
    pair = GenNet ("sai_ipu.ir / sai_spec",
                   fun () -> ph "bench/parserhawk/ir/sai_ipu.ir" sai_hdrs,
                             ParserHawkEval.sai_spec);
    want = Eq };

  { family = "ParserHawk"; name = "sai-cross";
    what = "SAI v4: the Tofino pipeline against the IPU one";
    pair = GenNet ("sai_tofino.ir / sai_ipu.ir",
                   fun () -> ph "bench/parserhawk/ir/sai_tofino.ir" sai_hdrs,
                             ph "bench/parserhawk/ir/sai_ipu.ir" sai_hdrs);
    want = Eq };
]

(* ------------------------------------------------------------------ *)
(* Timing. *)

let now () = Unix.gettimeofday ()

let median xs =
  let a = Stdlib.Array.of_list xs in
  Stdlib.Array.sort Stdlib.compare a;
  let n = Stdlib.Array.length a in
  if n = 0 then 0.0
  else if n mod 2 = 1 then a.(n / 2)
  else (a.((n / 2) - 1) +. a.(n / 2)) /. 2.0

type result = {
  c          : case;
  build_ms   : float;
  times_ms   : float list;
  got        : verdict;
  size_a     : IrSize.t;
  size_b     : IrSize.t;
  smt        : SmtSize.t;
  (* Where the check's time went, from the run whose time is the median.
     [SolveTime] accumulates per solve() call, so this is the whole check --
     a network checker issues one query, but nothing here assumes that. *)
  phases     : SolveTime.t;
}

let run_case reps (c : case) : result =
  let t0 = now () in
  (* Build both programs once, outside the timed region. *)
  let run, size_a, size_b =
    match c.pair with
    | Net (f1, f2) ->
      let p1 = gp f1 and p2 = gp f2 in
      (fun () -> of_smt (SmtModuleQuery.modnet_equivalence_checker p1 p2)),
      IrSize.of_general p1, IrSize.of_general p2
    | GenNet (_, mk) ->
      let p1, p2 = mk () in
      (fun () -> of_smt (SmtModuleQuery.modnet_equivalence_checker p1 p2)),
      IrSize.of_general p1, IrSize.of_general p2
  in
  let build_ms = (now () -. t0) *. 1000.0 in
  (* One extra run with the formula-size hook on, so measuring never lands in a
     reported time.  Its verdict is discarded; the timed runs below produce the
     one that is checked. *)
  SmtSize.reset ();
  SmtSize.enabled := true;
  let _ = run () in
  SmtSize.enabled := false;
  let smt = SmtSize.get () in
  let got = ref Eq and times = ref [] and phases = ref [] in
  for _ = 1 to reps do
    SolveTime.reset ();
    let s = now () in
    got := run ();
    let d = (now () -. s) *. 1000.0 in
    times := d :: !times;
    phases := (d, SolveTime.get ()) :: !phases
  done;
  let times_ms = Stdlib.List.rev !times in
  (* Report the breakdown from the run that produced the MEDIAN, so the parts
     and the total on one row describe the same execution.  Averaging the
     phases separately would let them disagree with the time beside them. *)
  let med = median times_ms in
  let closest =
    Stdlib.List.fold_left
      (fun best (d, ph) ->
         match best with
         | Some (bd, _) when Stdlib.abs_float (bd -. med)
                             <= Stdlib.abs_float (d -. med) -> best
         | _ -> Some (d, ph))
      None !phases in
  let phases = match closest with Some (_, ph) -> ph | None -> SolveTime.zero in
  { c; build_ms; times_ms; got = !got; size_a; size_b; smt; phases }

(* ------------------------------------------------------------------ *)
(* Output. *)

let print_header () =
  Stdlib.Printf.printf
    "%-11s %-21s %-13s %8s %6s %9s %9s %9s %9s  %-13s\n"
    "family" "case" "ir size" "smt" "depth" "load/ms" "query/ms" "z3/ms"
    "med/ms" "verdict";
  Stdlib.print_endline (Stdlib.String.make 124 '-')

let print_result r =
  let med = median r.times_ms in
  let ok = r.got = r.c.want in
  Stdlib.Printf.printf
    "%-11s %-21s %-13s %8d %6d %9.1f %9.1f %9.1f %9.1f  %-13s %s\n"
    r.c.family r.c.name (IrSize.to_short r.size_a)
    r.smt.SmtSize.dag r.smt.SmtSize.depth
    r.build_ms
    (SolveTime.build_ms r.phases) r.phases.SolveTime.solve_ms
    med (verdict_str r.got)
    (if ok then "" else "BAD want " ^ verdict_str r.c.want)

let csv_header =
  "family,case,what,verdict,expected,ok,build_ms,median_ms,min_ms,max_ms,reps,"
  ^ Stdlib.String.concat ","
      (Stdlib.List.map (fun s -> "a_" ^ s)
         (Stdlib.String.split_on_char ',' IrSize.header))
  ^ ","
  ^ Stdlib.String.concat ","
      (Stdlib.List.map (fun s -> "b_" ^ s)
         (Stdlib.String.split_on_char ',' IrSize.header))
  ^ "," ^ SmtSize.header ^ "," ^ SolveTime.csv_header

let csv_row r =
  let med = median r.times_ms in
  let mn = Stdlib.List.fold_left Stdlib.min infinity r.times_ms in
  let mx = Stdlib.List.fold_left Stdlib.max 0.0 r.times_ms in
  let q s = "\"" ^ s ^ "\"" in
  Stdlib.String.concat ","
    [ r.c.family; r.c.name; q r.c.what;
      verdict_str r.got; verdict_str r.c.want;
      (if r.got = r.c.want then "1" else "0");
      Stdlib.Printf.sprintf "%.3f" r.build_ms;
      Stdlib.Printf.sprintf "%.3f" med;
      Stdlib.Printf.sprintf "%.3f" mn;
      Stdlib.Printf.sprintf "%.3f" mx;
      Stdlib.string_of_int (Stdlib.List.length r.times_ms);
      IrSize.to_csv r.size_a; IrSize.to_csv r.size_b;
      SmtSize.to_csv r.smt; SolveTime.to_csv r.phases ]

(* ------------------------------------------------------------------ *)

let usage () =
  prerr_endline
    "usage: bench_eq [--family F] [--case SUBSTR] [--reps N] [--csv FILE] \
     [--list]";
  prerr_endline "  --family  TSS | P4 | eBPF | ParserHawk | Core";
  prerr_endline "  --case    run only cases whose name contains SUBSTR";
  prerr_endline "  --reps    timed repetitions per case (default 3)";
  prerr_endline "  --csv     also write a machine-readable row per case";
  prerr_endline "  --list    print the registry and exit, running nothing";
  prerr_endline "  --pair A B  time one ad-hoc pair of .ir files (no expected verdict)";
  prerr_endline "  --isolate run each case in its own process (slower, reproducible)";
  exit 2

let () =
  let family = ref "" and only = ref "" and reps = ref 3 in
  let csv = ref "" and list = ref false in
  let adhoc = ref [] in
  let isolate = ref false in
  let rec parse = function
    | [] -> ()
    | "--family" :: v :: r -> family := v; parse r
    | "--case" :: v :: r -> only := v; parse r
    | "--reps" :: v :: r -> reps := int_of_string v; parse r
    | "--csv" :: v :: r -> csv := v; parse r
    | "--list" :: r -> list := true; parse r
    | "--pair" :: a :: b :: r -> adhoc := [a; b]; parse r
    | "--isolate" :: r -> isolate := true; parse r
    | _ -> usage ()
  in
  parse (Stdlib.List.tl (Stdlib.Array.to_list Sys.argv));

  let contains hay needle =
    let nh = Stdlib.String.length hay and nn = Stdlib.String.length needle in
    if nn = 0 then true
    else
      let rec go i =
        if i + nn > nh then false
        else if Stdlib.String.sub hay i nn = needle then true
        else go (i + 1)
      in go 0
  in
  let selected =
    match !adhoc with
    | [a; b] ->
      (* An ad-hoc pair is timed and sized like any registry case, but carries
         no expected verdict -- there is nothing to check it against, so
         whatever it reports is accepted.  For a number going into the paper,
         add it to [cases] instead, where the verdict is pinned. *)
      [ { family = "adhoc"; name = Filename.remove_extension (Filename.basename a);
          what = a ^ " vs " ^ b; pair = Net (a, b); want = Eq } ]
    | _ ->
      Stdlib.List.filter
        (fun c ->
           (!family = "" || c.family = !family) && contains c.name !only)
        cases
  in

  if !list then begin
    Stdlib.Printf.printf "%-11s %-22s %-13s %s\n"
      "family" "case" "expected" "what";
    Stdlib.print_endline (Stdlib.String.make 100 '-');
    Stdlib.List.iter
      (fun c ->
         Stdlib.Printf.printf "%-11s %-22s %-13s %s\n"
           c.family c.name (verdict_str c.want) c.what)
      selected;
    Stdlib.Printf.printf "\n%d case(s).\n" (Stdlib.List.length selected);
    exit 0
  end;

  if selected = [] then begin
    prerr_endline "bench_eq: no cases matched"; exit 2 end;

  (* Cases share a process, and Z3's internal state does not fully reset
     between queries: a case's time depends on what ran before it.  Measured
     in one batch, [map-update-probe] came out at 237 ms and 1859 ms on either
     side of an unrelated change; run alone, both were within 20% of 2 s.  So
     any number going into a table wants [--isolate], which re-runs each case
     in a fresh process and collects its CSV row. *)
  if !isolate then begin
    print_header ();
    let bad = ref 0 and n = ref 0 in
    let rows = Stdlib.Buffer.create 4096 in
    Stdlib.List.iter
      (fun c ->
         let tmp = Filename.temp_file "bench_iso_" ".csv" in
         let out = Filename.temp_file "bench_iso_" ".txt" in
         let cmd =
           Stdlib.Printf.sprintf "%s --case %s --reps %d --csv %s > %s 2>&1"
             (Filename.quote Sys.executable_name)
             (Filename.quote c.name) !reps (Filename.quote tmp)
             (Filename.quote out) in
         let rc = Sys.command cmd in
         (* The child exits non-zero exactly when the verdict was wrong. *)
         if rc <> 0 then incr bad;
         incr n;
         (* Relay the child's own table row, so the two modes print alike. *)
         let oc = open_in out in
         (try
            while true do
              let l = input_line oc in
              let starts p =
                Stdlib.String.length l >= Stdlib.String.length p
                && Stdlib.String.sub l 0 (Stdlib.String.length p) = p in
              if starts c.family then
                (Stdlib.print_string (l ^ "\n"); raise Exit)
            done
          with End_of_file | Exit -> ());
         close_in oc; Sys.remove out;
         let ic = open_in tmp in
         (try
            let _hdr = input_line ic in
            Stdlib.Buffer.add_string rows (input_line ic ^ "\n")
          with End_of_file -> ());
         close_in ic;
         Sys.remove tmp;
         Stdlib.flush Stdlib.stdout)
      selected;
    if !csv <> "" then begin
      let oc = open_out !csv in
      output_string oc (csv_header ^ "\n");
      output_string oc (Stdlib.Buffer.contents rows);
      close_out oc;
      Stdlib.Printf.printf "\nwrote %s\n" !csv
    end;
    Stdlib.Printf.printf "\n%d case(s), %d with the expected verdict.\n"
      !n (!n - !bad);
    exit (if !bad > 0 then 1 else 0)
  end;

  print_header ();
  (* A case's .ir (or, for ParserHawk, its pipeline JSON) is a checked-in
     artifact produced by bench/<family>/regen.sh out of band; one that
     hasn't been regenerated yet -- or regenerated for a different family --
     shouldn't take the whole sweep down.  [run_case] reaches [open_in] before
     the timed region starts, so a missing file surfaces as [Sys_error] out of
     [run_case] itself; catch exactly that and skip the case instead. *)
  let skipped = ref [] in
  let results =
    Stdlib.List.filter_map
      (fun c ->
         match run_case !reps c with
         | r -> print_result r; Stdlib.flush Stdlib.stdout; Some r
         | exception Sys_error msg ->
           Stdlib.Printf.printf "%-11s %-21s SKIP (missing input: %s)\n"
             c.family c.name msg;
           Stdlib.flush Stdlib.stdout;
           skipped := c :: !skipped;
           None)
      selected
  in
  let bad =
    if !adhoc <> [] then []
    else Stdlib.List.filter (fun r -> r.got <> r.c.want) results in

  if !csv <> "" then begin
    let oc = open_out !csv in
    output_string oc (csv_header ^ "\n");
    Stdlib.List.iter (fun r -> output_string oc (csv_row r ^ "\n")) results;
    close_out oc;
    Stdlib.Printf.printf "\nwrote %s\n" !csv
  end;

  Stdlib.Printf.printf "\n%d case(s), %d with the expected verdict%s.\n"
    (Stdlib.List.length results)
    (Stdlib.List.length results - Stdlib.List.length bad)
    (if !skipped = [] then ""
     else Stdlib.Printf.sprintf ", %d skipped (missing input)"
            (Stdlib.List.length !skipped));
  if bad <> [] then begin
    Stdlib.List.iter
      (fun r ->
         Stdlib.Printf.printf "  BAD %s/%s: got %s, want %s\n"
           r.c.family r.c.name (verdict_str r.got) (verdict_str r.c.want))
      bad;
    exit 1
  end
