Installation notes: As JoeT mentioned, opam seems to work more reliably than brew on Mac.
Here's a minimal set of steps:
* opam install coq.8.20.1
* opam pin add coq 8.20.1
* opam install vscoq-language-server
* which vscoqtop

// Then install VSCoq extension for VS code
// then add the path for vscoqtop into the extension settings.

// You might need to install opam:
* sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

// You might need to initialize opam:
* opam init
* eval $(opam env)
* opam update

// Apparently the vscoq language server needs to be
// bumped up in version. Don't know why. But it still 
// works with the old version.