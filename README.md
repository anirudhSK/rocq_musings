## Usage

**Prerequisites (macOS)**
Install a package manager and pkg-config:
```bash
# Homebrew (preferred)
 /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
 eval "$(/opt/homebrew/bin/brew shellenv)" 
 # or follow whatever the brew install script says re: eval ...
 brew install pkg-config
```
(Or build local: pkgconf as shown below if brew unavailable.)

**Install opam (choose ONE)**
```bash
brew install opam
# or user-local:
curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh | sh -s -- --prefix="$HOME/.local"
```

**Initialize opam**
```bash
opam init -y
eval $(opam env)
opam update
```

**Install Coq + VSCoq language server**
```bash
opam install -y coq.9.1.0 vsrocq-language-server
which vscoqtop
```
(Pinning after specifying a version is unnecessary.)

**Initialize VSCode**
* Install VSCoq extension for VS code
* Then add the path for vscoqtop into the extension settings.
* You can do this by pasting the output of 'which vscoqtop' into the path box in the extension settings.

**Build Rocq code**
```bash
rocq makefile -f _CoqProject *.v -o Makefile
make -j
```

**For OCaml code, to interface with Z3 after extraction**
* opam install z3 ppx_import sexplib ppx_sexp_conv ppx_expect
* ocamlfind ocamlc -thread -package z3 -linkpkg -o smt_query smt_query.ml

**Build extracted code**
```bash
# if there are new files that have been extracted via make
# then you must update the dune dependencies
perl sync_dune_modules.pl

# check that code builds
dune build --profile release

# usage: dune exec eq_check ./path/to/s/exp/1 ./path/to/s/exp/2
dune exec eq_check test/prog1.out test/prog1.out
# -> Equivalent
dune exec eq_check test/prog1.out test/prog2.out
# -> ┌ SAT Valuation
# -> | var( hdr_1 ) := 0
# -> └
# -> Not Equivalent

# run tests with
dune runtest
```

**Configure Git Repo**

To prevent pushing old versions of the P4C compiler due to git not updating it, configure an automatic submodule update for this repo.
`git config submodule.recurse true`


// Apparently the vscoq language server needs to be
// bumped up in version. Don't know why. But it still 
// works with the old version.

## Adding Tests

You can add new expect tests of form:
```
let%expect_test "<new test name>" =
  <code that prints something to terminal>
  [%expect {| <what you expect to get printed> |}]
```
into `extracted_code/Test{Module/Program}Semantics.ml`. You can also add tests to a new `.ml` file and include it in the `semantics_tests` library in `extracted_code/dune`.

Two things to know before you fight the build:

* **Do not hand-edit the module lists in `extracted_code/dune`.**  `sync_dune_modules.pl` regenerates them by checking for `!/extracted_code/*.ml` in `.gitignore`, so a new hand-written `.ml` needs to be tracked before running the script.
* **A new module test program needs two lines, not three.**  `Extraction.v` extracts `TestModulePrograms.lookup_mod_test_program`, a `string -> option GeneralCaracaraProgram`, rather than individual programs — so the name-to-key encoding stays on the Rocq side and there is nothing to mirror in OCaml. Add the program to `mod_test_program_list` in the Rocq file, and bind a name for it in `extracted_code/ModProgs.ml`. Order in the list does not matter, an unknown name fails loudly, and an expect test lists the registry so that adding a program without binding it is noticed too.

If the test program that you add isn't well-formed, the test harness will print `(<pid>) malformed` before the test body, so either a) if the program is intentionally malformed, this must be added to the expected output or b) you should fix your program or c) if you believe the program is well-formed, open an issue. 

# Memory

Loads and stores are part of the base IR. A program declares the memory regions it can
address, and a region is named statically while the offset within it is a runtime value:

```coq
GeneralCaracaraProgramDef 16 [mkMemRegionDecl (MemRegionCtr 1) 4] net
...
  LoadOp  u8 (MemRegionCtr 1) (OpConst (repr 2)) (HeaderCtr 2)
  StoreOp u8 (MemRegionCtr 1) (OpConst (repr 2)) (OpHeader (HeaderCtr 1))
```

A region is an array of bytes: a width-`ty` access covers `it_bytes ty` consecutive
cells, little-endian, so a `u16` store is exactly the two `u8` stores an optimiser
coalesces it from. Static provenance plus a dynamic offset is how eBPF actually works — the verifier fixes
which object a pointer refers to before the program runs — so `CrVal` has no pointer
constructor at all. Memory lives on `GeneralProgramState` (`sh_mem`, a region → contents
map) rather than on `TransformerState`, because `TransformerState T` is homogeneous in one
element type and a region's contents are not of that type; it is threaded into a
transformer alongside the state, forwarded in and copied back out the same way the header
map is.

Both operations are **total**. An access outside the region's declared length yields
`ErrorVal` (load) or is dropped (store), and neither clears `gps_valid`. See
`SOUNDNESS.md` for why a partial operation would be unsound here rather than merely
conservative.

What distinguishes a program that walks off the end is instead `sh_mem_extent`: per region,
how many bytes of it the run required — one past the largest offset touched, in bounds or
not, so 0 means the region was never touched at all. This is the memory analogue of
`sh_bits_read`, and equivalence compares it — if you hand two programs the same buffer and
one reads further into it, they are not interchangeable, because one can fault where the
other does not. Equivalence also compares each declared region's final contents, cell by
cell, since a region is an observable side effect rather than internal scratch.

A separate, older memory IR (`CrMem.v`, `MemSolver.ml`) used to sit alongside this one with
its own syntax, solver and test path. It was removed once the eBPF transpiler stopped
targeting it; its examples live on as the `mem_*` module test programs.

## eBPF

The transpiler in `~/proj/ect` compiles eBPF bytecode into this IR:
`bpf_to_ir <obj.o>` writes a `GeneralCaracaraProgram` s-expression. A register
becomes one `u64` header, the context and the packet become declared regions, the BPF
stack becomes one header per slot (it is private scratch, and comparing it would report
`-O0` and `-O2` as differing over a spill nothing can observe), and control flow becomes a
chain of transformer modules guarded on a program-counter header — a transformer runs only
the first rule that matches, so sequencing has to come from the chain. That repo's README
has the details and the list of unsupported instructions.

To check a pair:

```bash
./_build/default/extracted_code/EqCheck.exe --net path/to/a.ir path/to/b.ir
```

`test/bpf_O0.ir` and `test/bpf_O2.ir` are the two lowerings of `test/bpf_ref.c`, checked
in `TestEquality` ("e2e bpf test: O0 ≡ O2, unified IR") and run concretely in
`TestModuleSemantics` — the verdict alone would also be satisfied by two programs that are
equally broken, so both halves are needed.

Two departures from the derived sexp encoding make a program writable from outside this
tree, both in `extracted_code/CrTypeIF.ml`: numbers are decimal on the way out and either
decimal or Coq-encoded on the way in (a `nat` input length would otherwise be 64 nested
`S`s), and `ModuleNetwork.net_edges` — a *function*, so the derived converters are
sexplib's arrow stubs and reading one back was impossible — is written as an explicit edge
list.

# Execution Semantics

There are two execution domains: symbolic and concrete. These two execution domains are intended to be connected via a soundness and a completeness lemma.

Essentially, these lemmas boil down to executing the symbolic programs, running an equivalence query between the two resultant symbolic states, and proving that Z3's result either guarantees that all concrete executions will be identical, or at least one concrete execution will differ. They more or less connect `eval_general_program_symbolic` to `eval_general_program_concrete`

Execution consumes and emits program state. `GeneralProgramState` is a bundle of a global header map, a global read tape, a global write tape, a count of how many bits have been read off the input packet, the memory (contents and access extents, per declared region), each module's local state, and a validity flag. It is parameterised by the header-value type `Th`, the packet-bit type `Tb`, and the memory-contents type `Tm`, which is what lets the concrete and symbolic domains share one definition: concretely `(CrVal, bool, Array CrVal)`, symbolically `(SmtArithExpr, ConditionalVal SmtBoolExpr, SmtArrExpr)`. Within state, `sh_bits_read` is typed `Th` rather than `nat` because the amount consumed is data-dependent. Also, `gps_valid` is the network's accept flag: a parser that rejects clears it, and a cleared flag stops the recursion.

Right now, the semantics assume a linear chain topology (e.g. we don't collect traces when there is fan-in/fan-out, and we have no notion of coherent shared state across parallel modules). A well-formed network additionally ends at deparsers (`wf_module_networkb`), so a program's output is always a packet.

It used to have to *start* at a parser too, making the input always a packet. That was dropped once memory arrived: a program can take its input from a declared region instead, and an eBPF program does exactly that — requiring a parser source only forced a stub that accepts immediately and extracts nothing. The evaluator never cared, since it dispatches on each module's kind as it reaches it. The output side has not had the same treatment, so a network whose result is purely a region still needs a deparser to be considered well-formed; that asymmetry is untouched rather than intended.

## Concrete Semantics

As a high-level overview we have something like:

```
eval_network_from_concrete net start f_hdrs f_bits gs fuel :=
  (* stop if out of fuel, or if some upstream module already rejected *)
  if fuel = 0 || not (gps_valid gs) then None else
  match lookup_module net start, mod_states gs ?? start with
  | Some m, Some ls ->
      (* a module sees the header map and packet handed down its incoming edge *)
      let ls = set_module_packet (set_module_header_map ls f_hdrs) f_bits in
      let gs =
        match m, ls with
        | transformer, TransformerMod ts ->
            eval_transformer_concrete;
            publish the updated headers
        | parser, ParserMod ps ->
            eval_parser_concrete;
            publish the updated headers, the residual read tape,
            and add the cursor to sh_bits_read
            (on reject: clear gps_valid)
        | deparser, DeparserMod ds ->
            eval_deparser_concrete;
            publish the emitted bits as the write tape
        | definition/state mismatch -> clear gps_valid
      in
      (* hand this module's headers and residual to each downstream module *)
      fold eval_network_from_concrete over (downstream_modules net start)
  | _ -> None
```

After some bootstrapping, `eval_network_from_concrete` recurses through the network graph. Fuel is the module count, which bounds the walk.

Each module has a definition and a state, and they have to agree: a `ParserModule` paired with a `TransformerMod` state is a malformed network.

There are two distinct failure channels:

* **`None`:** the walk could not proceed at all (no fuel or module/state not found).
* **`gps_valid := false`:** the run executed, but the packet was not accepted (parser rejected, module definition and state did not match).

The recursion refuses to continue once `gps_valid` is clear, so in a chain the second turns into the first at the next hop. The exception is a sink: if the last module clears the flag there is no next hop, and you get `Some` state with `gps_valid = false` and whatever tapes were published before that point. Code that inspects a result therefore has to check both (`Some` is not automatically an accepted packet).

The distinction matters because rejection is packet-dependent and is part of what two programs must agree on, whereas `None` means the program does not run at all.

### Transformer Modules

`eval_transformer_concrete` selects the **first** rule whose match pattern holds and runs its action list left to right; if no rule matches, the state is unchanged. Ordering therefore encodes priority.

Match comparisons go through `CrVal.eqb` / `CrVal.ltb`, which compare the `CrIntType` **before** the value. A couple consequence of this:

- matching is first constrainted by type (e.g. a header extracted at `u64` never matches a `u8` constant).
- a header no module ever writes is `UninitVal`, and `eqb`/`ltb` are false on `UninitVal`, so it matches nothing.

`TestModuleSemantics` pins both down (`match guard: ...`). This behavior might be worth adjusting in the future, but for now it's just preserved for posterity.

### Parser Modules

`eval_parser_concrete` runs the state machine from `parser_start`. Each action advances a cursor: `SeekForward` skips bits, `ExtractOpConstructor h width ty` reads `width` bits into header `h` at type `ty`. Reading past the end of the packet fails the parse, as does a `Reject` transition. Both clear `gps_valid`.

On `Accept`, the bits after the cursor become the **residual**, which is handed downstream as the next module's read tape, and the cursor is added to the network's `sh_bits_read`. Chained parsers therefore each consume a prefix of what the previous one left, and `sh_bits_read` accumulates across the whole chain.

### Deparser Modules

`eval_deparser_concrete` concatenates the bits of each emit, MSB first, and that is the module's output packet. The unconsumed payload is **not** appended — the output packet is exactly what was emitted.

That is a statement about the output packet only, not about the payload disappearing. A deparser publishes `sh_write_tape` and nothing else: it never touches `sh_read_tape`, so the residual the last parser left is still sitting in the general state when the network finishes (and is what would be handed on, were a deparser not a sink). The only thing the deparser overwrites is its own module-local `p_packet`, which held the residual on entry and holds the emitted bits on exit.

A deparser **appends** to `sh_write_tape` rather than replacing it, so a network containing more than one deparser emits the concatenation of what each wrote, in the order they run. The tape starts empty, so this is invisible to a single-deparser network. Note that `wf_module_networkb` only requires *sinks* to be deparsers, so a deparser in the middle of a chain is well-formed and its output is kept. A chained pair emitting `h1` then `h2` is equivalent to a single deparser emitting `h1, h2`, which is checked both concretely and through the equivalence checker.

So for a 24-bit input `[0xAA, 0xBB, 0xCC]` into a pipeline that extracts one byte and emits it, you end with `sh_write_tape = [0xAA]`, `sh_bits_read = 8`, and `sh_read_tape = [0xBB, 0xCC]` still intact.

The residual is deliberately not part of what equivalence compares — but nothing is lost by that, because both programs are run against the *same* symbolic input bits (`symbolic_input_bits` names them `pkt_1 ...` with no per-program prefix) and the checker already requires equal declared input lengths. Equal `sh_bits_read` on the same packet therefore means the residuals are the same suffix of the same bits, so comparing them would add nothing that `check_sym_bits_read` does not already say.

A deparser is total: emitting a header that holds no integer (never written, or an `ErrorVal` from a type-mismatched op) yields zero bits rather than failing. That is a deliberate choice with a real trade-off attached; the comment on `eval_deparser_concrete` carries the argument.

## Example
This is a simple program that does an 8-bit add of the first 8 bits of a packet and write it to a 0-padded 32 bit output packet.
```
GeneralCaracaraProgram
  8
  {
    net_modules := [
      (* read 8 bits into header 1 *)
      ParserModule (ModuleNameCtr 1) {
        parser_start := ParserStateLabelCtr 1;
        parser_states := [
          {
            psd_label := ParserStateLabelCtr 1;
            psd_action := Some (ExtractOpConstructor (HeaderCtr 1) 8 u8);
            psd_trans := Unconditional Accept;
          }
        ]
      },
      (* add header 1 to itself and store in place *)
      TransformerModule (ModuleNameCtr 2) [] [] [
        Seq (SeqCtr [] [StatelessOp
          AddOp
          u8
          (OpHeader (HeaderCtr 1))
          (OpHeader (HeaderCtr 1))
          (HeaderCtr 1)
        ])
      ],
      (* dump header 1 into a 32 bit 0-padded output packet *)
      DeparserModule (ModuleNameCtr 3) {
        deparser_emits := [
          EmitOpConstructor (HeaderCtr 1) 32
        ]
      },
    ];
    net_edges := (fun a b =>
      match (unwrap a), (unwrap b) with
      | 1, 2 => true
      | 2, 3 => true
      | _, _ => false
      end);
    start_module := ModuleNameCtr 1;
  }
```

If we consider what we should consider an equivalent program, it would be pretty natural to say something like: they should take in the same size of input packet, and regardless of what the actual bit values are of that input packet, the bits of the output packet should be identical.

In this light, the only way in which two equivalent programs are allowed to differ is internally. How many modules they use, how the work is split between parsing and transforming, which header slots hold intermediate values, what order the rules are written in — none of that is observable. What is observable is only: did the packet get accepted, what bits came out, and how much of the input was read.

## Symbolic Semantics

`eval_general_program_symbolic` mirrors the concrete walk module for module, over `SmtArithExpr` header values and `ConditionalVal SmtBoolExpr` packet bits. The differences all come from path merging:

- A parser never fail-closes. Data-dependent `select` control flow is merged into a single header map with `SmtConditional`, and rejection becomes a symbolic predicate (`spr_accept`) conjoined into `gps_valid` rather than a control-flow abort. Correspondingly there is no `gps_valid` guard on the recursion — validity is a formula, not a decidable bool, so execution always proceeds and merges every path.
- A residual is a list of bits each carrying a presence condition (`cvc`), so a variable-length tail is representable: `merge_bitstream` pads the shorter side with absent positions. This is why a padded position must not be silently readable — extracting from one forces the accept condition false.
- `sh_bits_read` merges with `SmtConditional`, so a parser that consumes a different number of bits on different paths yields a genuinely symbolic count.

`concretize_sym_modnet_state` maps a symbolic state back to a concrete one under a valuation, which is what lets equivalence be stated over concretized outputs.

## Equivalence

`modnet_equivalence_checker p1 p2` first requires the two programs to declare the same input length; otherwise they are not comparable and it answers `NotEquivalentVariablesDiffer`. It then runs both symbolically from their initial states and asks Z3 for a packet making the two observably differ. `Unsat` means no such packet exists, so `Equivalent`; a model is returned as `NotEquivalent f`.

Two runs count as agreeing when either both rejected, or both accepted and

- their output packets are equal (`sym_out_equal`, comparing presence conditions as well as bit values, so differing output *lengths* count as differing),
- they read the same number of bits (`check_sym_bits_read`),
- every declared memory region holds the same contents (`check_sym_mem_equal`), and
- they required the same number of bytes of every region (`check_sym_mem_extent`).

The read-extent conjunct is the bitstream analogue of the memory access-extent equivalence described above: a network that reads further into its input needs more of it to be there, so two networks that emit identical packets while consuming different amounts are not interchangeable.

The checker also refuses to compare two programs whose declared regions differ, the same way it refuses when their input lengths differ: the two runs share one set of region input variables, so the comparison would not be meaningful otherwise.

Note the shape of that condition — "both rejected" is an accepting case, which is correct but makes the checker only as good as its notion of validity. Any imprecision in `gps_valid`, in *either* direction, is unsound: over-approximating acceptance compares outputs that concretely never happened, and under-approximating it hides real differences inside the both-rejected case. That is why the deparser has no validity condition on either side rather than an approximate one.

The soundness and completeness lemmas at the bottom of `SmtModuleQuery.v` state exactly this correspondence, and both are proved. Note what they cover: they relate the checker's verdict to the concretization of the *symbolic* final states, not to a concrete run — see `SOUNDNESS.md`.

A caveat worth internalising when adding tests: a program that rejects every packet is equivalent to any other program that rejects every packet. It is easy to write two "equivalent" programs that are both simply broken, and the checker will agree with you. `TestModuleSemantics` therefore checks concrete outputs for the classifier examples rather than relying on the checker alone.
