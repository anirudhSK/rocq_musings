#!/bin/bash

# Default values
P4_FILE="main.p4"
P4_COMPILER="./p4c/build/p4dummy"
CONVERTER="convert.py"
DEBUG=false

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --debug)
            DEBUG=true
            shift
            ;;
        --file)
            P4_FILE="$2"
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
            echo "Usage: $0 [OPTIONS] [FILE]"
            echo "Options:"
            echo "  --file FILE       P4 file to compile (default: main.p4)"
            echo "  --compiler PATH   P4 compiler path (default: ./p4c/build/p4dummy)"
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
if [ ! -f "$P4_FILE" ]; then
    echo "Error: P4 file '$P4_FILE' not found" >&2
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

debug_echo "Compiling P4 file: $P4_FILE"
debug_echo "Using compiler: $P4_COMPILER"
debug_echo "Using converter: $CONVERTER"

# Create output directory if it doesn't exist
OUTPUT_DIR="../$(basename "$PWD")"
mkdir -p "$OUTPUT_DIR"

OUTPUT_FILE="$OUTPUT_DIR/main.v"
debug_echo "Output file: $OUTPUT_FILE"

# Step 1: Run P4 compiler and capture stdout to main.v
debug_echo "Running P4 compiler..."
if ! "$P4_COMPILER" "$P4_FILE" > "$OUTPUT_FILE" 2>/dev/null; then
    echo "Error: P4 compilation failed" >&2
    exit 1
fi

if [ "$DEBUG" = false ]; then
    echo "P4 compilation completed"
fi

# Step 2: Run coqc on the generated file and pipe stdout to converter
debug_echo "Running coqc on $OUTPUT_FILE..."
if [ "$DEBUG" = true ]; then
    coqc "$OUTPUT_FILE" 2>/dev/null | python3 "$CONVERTER" --debug
else
    coqc "$OUTPUT_FILE" 2>/dev/null | python3 "$CONVERTER" >/dev/null 2>&1
fi

COQC_EXIT_CODE=${PIPESTATUS[0]}
CONVERTER_EXIT_CODE=${PIPESTATUS[1]}

if [ $COQC_EXIT_CODE -ne 0 ]; then
    echo "Error: coqc failed" >&2
    exit 1
fi

if [ $CONVERTER_EXIT_CODE -ne 0 ]; then
    echo "Error: converter failed" >&2
    exit 1
fi

if [ "$DEBUG" = false ]; then
    echo "Conversion completed successfully"
fi