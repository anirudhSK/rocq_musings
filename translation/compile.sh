#!/bin/bash
set -e

# Default values
P4_FILE_FIRST="first.p4"
P4_FILE_SECOND="second.p4"
P4_COMPILER="./p4c/build/rocq"

OUTPUT_FILE_FIRST="./first.out"
OUTPUT_FILE_SECOND="./second.out"

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --first)
            P4_FILE_FIRST="$2"
            shift 2
            ;;
        --second)
            P4_FILE_SECOND="$2"
            shift 2
            ;;
        --compiler)
            P4_COMPILER="$2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS]"
            echo "Options:"
            echo "  --first FILE       P4 file to compile (default: first.p4)"
            echo "  --second FILE       P4 file to compile (default: second.p4)"
            echo "  --compiler PATH   P4 compiler path (default: ./p4c/build/rocq)"
            echo "  -h, --help       Show this help message"
            echo ""
            echo "If FILE is provided as positional argument, it overrides --file option"
            exit 0
            ;;
        -*)
            echo "Error: Unknown option $1" >&2
            exit 1
            ;;
        *)
            # Positional argument - treat as P4 file
            P4_FILE="$1"
            shift
            ;;
    esac
done

# Debug output function
debug_section() {
        echo -e "\n\n------------ $@ ------------\n\n"
}

# Check if P4 file exists
if [ ! -f "$P4_FILE_FIRST" ]; then
    echo "Error: P4 file '$P4_FILE_FIRST' not found" >&2
    exit 1
fi


# Check if P4 file exists
if [ ! -f "$P4_FILE_SECOND" ]; then
    echo "Error: P4 file '$P4_FILE_SECOND' not found" >&2
    exit 1
fi


# Check if P4 compiler exists
if [ ! -f "$P4_COMPILER" ]; then
    echo "Error: P4 compiler '$P4_COMPILER' not found" >&2
    exit 1
fi


# Clean enviorment
debug_section "Cleaning the enviorment"
rm -f  "$OUTPUT_FILE_FIRST" "$OUTPUT_FILE_SECOND"


# Compile first P4 file
debug_section "Compiling first P4 file: $P4_FILE_FIRST"
echo "Using compiler: $P4_COMPILER"
echo "Using converter: $CONVERTER"
echo "Output file: $OUTPUT_FILE_FIRST"
echo "Running P4 compiler..."

"$P4_COMPILER" "$P4_FILE_FIRST" > /dev/null
mv output.sexp "$OUTPUT_FILE_FIRST"

echo "P4 compilation completed"


# Compile second P4 file
debug_section "Compiling second P4 file: $P4_FILE_SECOND"
echo "Output file: $OUTPUT_FILE_SECOND"
echo "Running P4 compiler..."

"$P4_COMPILER" "$P4_FILE_SECOND" > /dev/null
mv output.sexp "$OUTPUT_FILE_SECOND"

echo "P4 compilation completed"