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
* Install VSCoq extension
* Set the path to `vscoqtop` if not auto-detected.

**Build code**
```bash
coq_makefile -f _CoqProject *.v -o Makefile
make -j
```