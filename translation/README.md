## Usage
To compile the file `main.v` run the command `./compile.sh`
#### Custom arguments
```
Usage: ./compile.sh [OPTIONS] [FILE]
Options:
  --file FILE       P4 file to compile (default: main.p4)
  --compiler PATH   P4 compiler path (default: ./p4c/build/p4dummy)
  --converter PATH  Python converter script (default: convert.py)
  --debug          Enable debug output
  -h, --help       Show this help message
```

## Compilation steps
1. P4 -> ROCQ using the custom P4 compiler extension.
1. ROCQ -> ROCQ SMT IR using eval compute in the main.v file.
1. ROCQ SMT IR -> Z3 using a compiler writein in convert.py
1. Z3 -> Final result using a Z3 evaluator to return either sat/unsat