## Usage
**Install Rocq**
* sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

**Initialize opam**
* opam init
* eval $(opam env)
* opam update

**Install coq**
* opam install coq.8.20.1
* opam pin add coq 8.20.1
* opam install vscoq-language-server
* which vscoqtop

**Initialize VSCode**
* Install VSCoq extension for VS code
* Then add the path for vscoqtop into the extension settings.

**Build code**
* coq_makefile -f _CoqProject *.v -o Makefile
* make

// Apparently the vscoq language server needs to be
// bumped up in version. Don't know why. But it still 
// works with the old version.