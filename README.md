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


// Apparently the vscoq language server needs to be
// bumped up in version. Don't know why. But it still 
// works with the old version.
