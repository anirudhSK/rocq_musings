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
opam install -y coq.8.20.1 vscoq-language-server
which vscoqtop
```
(Pinning after specifying a version is unnecessary.)

**Initialize VSCode**
* Install VSCoq extension for VS code
* Then add the path for vscoqtop into the extension settings.
* You can do this by pasting the output of 'which vscoqtop' into the path box in the extension settings.

**Build Rocq code**
```bash
coq_makefile -f _CoqProject *.v -o Makefile
make -j
```

**For OCaml code, to interface with Z3 after extraction**
* opam install z3 ppx_import sexplib ppx_sexp_conv
* ocamlfind ocamlc -thread -package z3 -linkpkg -o smt_query smt_query.ml

**Build extracted code**
```bash
dune build --profile release

# usage: dune exec eq_check ./path/to/s/exp/1 ./path/to/s/exp/2
dune exec eq_check extracted_code/ref/crcr1.out extracted_code/ref/crcr1.out
# -> Equivalent
dune exec eq_check extracted_code/ref/crcr1.out extracted_code/ref/crcr2.out
# -> Not Equivalent

# Run tests
dune exec run_tests
```

**Configure Git Repo**

To prevent pushing old versions of the P4C compiler due to git not updating it, configure an automatic submodule update for this repo.
`git config submodule.recurse true`


// Apparently the vscoq language server needs to be
// bumped up in version. Don't know why. But it still 
// works with the old version.

## Adding Tests

In `./extracted_code/RunTests.ml`, to add a new test, write a new
```
let () = register "<test_name>" (fun () ->
  <test_body>)
```
where test_body should return `1` if it passes and `0` if it fails.

`get_program` and `get_mem_program` are useful helpers for reading in s-expression program representations.

# Memory IR

The memory IR mirrors a subset of the base IR but introduces the notion of loads, stores, and data types (e.g. you can have a uint8, but you can also have a pointer). 

The notion of a "program" in this IR is a function body, a set of IO variables, absolute memory addresses, and variable memory addresses. That is, it contains both the state transformer as well as possible side effects.

A new type, CrVal, was introduced that encodes integers of various byte widths as well as pointers.

The notion of equivalence for two programs has been extended for memory programs to include equivalence of memory access extents, that is, if you pass in a pointer for example, for two programs to be identical, the greatest offset into that pointer used by the programs should be the same (since otherwise there could be a segfault on one and not the other).
