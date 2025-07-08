## Usage
To compile the file `first.p4` and `second.p4` into `first_generated.v` and `second_generated.v` combined in `combine.v` and verfied through SMT, run the command `./compile.sh` from the translation directory. This will output either unsat (equivalent programs) or sat. Adding the `--debug` flag will include further Z3 output.

#### Limitations
The variable names in the combination file are hardcoded. Thus, any changes to reference names in either `first.p4` or `second.p4` will need to be manually changed in `combine.v`.

#### Custom arguments
```
Usage: ./compile.sh [OPTIONS]
Options:
  --first FILE       P4 file to compile (default: first.p4)
  --second FILE       P4 file to compile (default: second.p4)
  --compiler PATH   P4 compiler path (default: ./p4c/build/rocq)
  --converter PATH  Python converter script (default: convert.py)
  --debug          Enable debug output
  -h, --help       Show this help message

If FILE is provided as positional argument, it overrides --file option
```

## Compilation steps
1. P4 -> ROCQ using the custom P4 compiler extension.
1. ROCQ -> ROCQ SMT IR using eval compute in the main.v file.
1. ROCQ SMT IR -> Z3 using a compiler writein in convert.py
1. Z3 -> Final result using a Z3 evaluator to return either sat/unsat