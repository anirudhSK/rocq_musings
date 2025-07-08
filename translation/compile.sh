#!/bin/bash

# Default values
P4_FILE_FIRST="first.p4"
P4_FILE_SECOND="second.p4"
P4_COMPILER="./p4c/build/rocq"
CONVERTER="convert.py"
DEBUG=false

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --debug)
            DEBUG=true
            shift
            ;;
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
        --converter)
            CONVERTER="$2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS]"
            echo "Options:"
            echo "  --first FILE       P4 file to compile (default: first.p4)"
            echo "  --second FILE       P4 file to compile (default: second.p4)"
            echo "  --compiler PATH   P4 compiler path (default: ./p4c/build/rocq)"
            echo "  --converter PATH  Python converter script (default: convert.py)"
            echo "  --debug          Enable debug output"
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
debug_echo() {
    if [ "$DEBUG" = true ]; then
        echo "$@"
    fi
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

# Check if converter exists
if [ ! -f "$CONVERTER" ]; then
    echo "Error: Converter script '$CONVERTER' not found" >&2
    exit 1
fi

# Compile first P4 file
debug_echo "Compiling P4 file: $P4_FILE_FIRST"
debug_echo "Using compiler: $P4_COMPILER"
debug_echo "Using converter: $CONVERTER"

OUTPUT_FILE="../first_generated.v"
debug_echo "Output file: $OUTPUT_FILE"

debug_echo "Running P4 compiler..."

(exec 2>/dev/null; "$P4_COMPILER" "$P4_FILE_FIRST" > "$OUTPUT_FILE") || true

debug_echo "P4 compilation completed"


# Compile second P4 file
debug_echo "Compiling P4 file: $P4_FILE_SECOND"

OUTPUT_FILE="../second_generated.v"
debug_echo "Output file: $OUTPUT_FILE"

debug_echo "Running P4 compiler..."

(exec 2>/dev/null; "$P4_COMPILER" "$P4_FILE_SECOND" > "$OUTPUT_FILE") || true

debug_echo "P4 compilation completed"

# Add combination file to main dir
COMBINATION_FILE="../combine.v"
cp ./combine.v $COMBINATION_FILE

# Make coq files
(exec 2>/dev/null;coq_makefile -f _CoqProject *.v -o Makefile > /dev/null)
(exec 2>/dev/null; make -C ../ > /dev/null)


# Run coqc on the generated file and pipe stdout to converter
debug_echo "Running coqc on $COMBINATION_FILE..."
if [ "$DEBUG" = true ]; then
    coqc -R .. MyProject  "$COMBINATION_FILE" 2>/dev/null | python3 "$CONVERTER" --debug
else
    coqc -R .. MyProject  "$COMBINATION_FILE" 2>/dev/null | python3 "$CONVERTER"
fi

if [ "$DEBUG" = true ]; then
    echo "Conversion completed successfully"
fi