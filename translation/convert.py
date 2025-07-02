import argparse
import re
from z3 import *

def parse_smt(tokens):
    """
    Recursively parses a list of tokens representing the SMT expression.
    """
    token = tokens.pop(0)

    if token == 'SmtBoolNot':
        expr = parse_smt(tokens)
        return f"(not {expr})"
    elif token == 'SmtBoolAnd':
        expr1 = parse_smt(tokens)
        expr2 = parse_smt(tokens)
        return f"(and {expr1} {expr2})"
    elif token == 'SmtBoolEq':
        expr1 = parse_smt(tokens)
        expr2 = parse_smt(tokens)
        return f"(= {expr1} {expr2})"
    elif token == 'SmtConditional':
        cond = parse_smt(tokens)
        then_expr = parse_smt(tokens)
        else_expr = parse_smt(tokens)
        return f"(ite {cond} {then_expr} {else_expr})"
    elif token == 'SmtBitAdd':
        expr1 = parse_smt(tokens)
        expr2 = parse_smt(tokens)
        return f"(bvadd {expr1} {expr2})"
    elif token == 'SmtConst':
        # Extract the integer value from the constant definition
        # This is a simplified extraction, assuming the format is consistent
        const_def = tokens.pop(0)
        match = re.search(r'intval\s*:=\s*(-?\d+)', const_def)
        if match:
            val = int(match.group(1))
            # Format as a 32-bit hex value for Z3
            return f"#x{val:08x}"
        else:
            raise ValueError(f"Could not parse SmtConst value from: {const_def}")
    elif token == 'SmtTrue':
        return "true"
    else:
        # This handles the case where a token might be part of a constant's structure
        # and should be skipped. The main logic relies on the keyword tokens.
        return ""


def clean_up_extra_spaces(s):
    """
    Removes redundant spaces for cleaner output.
    """
    return re.sub(r'\s+', ' ', s).replace('( ', '(').replace(' )', ')')

def compile_rocq_to_z3(rocq_string):
    """
    Compiles a Rocq SMT string to a Z3 SMT-LIB formatted string.
    """
    # Pre-process the string to make it easier to tokenize
    # Remove newlines, extra whitespace, and the outer smt_query wrapper
    rocq_string = rocq_string.strip()
    if rocq_string.startswith("= smt_query"):
        rocq_string = rocq_string[len("= smt_query"):].strip()
    if rocq_string.endswith(": option SmtValuation"):
        rocq_string = rocq_string[:-len(": option SmtValuation")].strip()

    # Replace parentheses and brackets with spaces for easier splitting
    rocq_string = rocq_string.replace('(', ' ( ').replace(')', ' ) ')
    rocq_string = rocq_string.replace('{', ' { ').replace('}', ' } ')

    # Tokenize the input string based on whitespace
    # We also group the SmtConst value block into a single "token"
    tokens = []
    in_const_block = False
    block = ""
    for part in rocq_string.split():
        if part == '{':
            in_const_block = True
            block = part
        elif part == '}':
            in_const_block = False
            block += " " + part
            tokens.append(block)
        elif in_const_block:
            block += " " + part
        else:
            tokens.append(part)

    # Filter out parentheses and empty tokens
    filtered_tokens = [t for t in tokens if t not in ['(', ')', '']]

    # Start parsing from the top-level expression
    if not filtered_tokens:
        return "; Empty input"

    parsed_expression = parse_smt(filtered_tokens)

    # Assemble the final Z3 script
    z3_script = f"""
(set-logic QF_BV)

; The main assertion - we're asking Z3 to find a model where this is TRUE
; If Z3 says "unsat", then no such model exists (programs are equivalent)
; If Z3 says "sat", then it found a counterexample

(assert 
  {parsed_expression}
)

(check-sat)
(exit)
"""
    return z3_script.strip()

def debug_print(message, debug_mode):
    """Print debug messages only when debug mode is enabled"""
    if debug_mode:
        print(f"[DEBUG] {message}", file=sys.stderr)

def main():
    # Set up argument parsing
    parser = argparse.ArgumentParser(description='Process compilation output')
    parser.add_argument('--debug', 
                       action='store_true', 
                       help='Enable debug mode')
    
    # Parse arguments
    args = parser.parse_args()
    
    # Extract values
    debug_mode = args.debug
    
    # Read coqc output from stdin
    debug_print("Reading coqc output from stdin...", debug_mode)
    coqc_output = sys.stdin.read()
    
    debug_print("Python script started", debug_mode)
    debug_print(f"Received coqc output length: {len(coqc_output)} characters", debug_mode)
    debug_print(f"Debug mode: {debug_mode}", debug_mode)

    # Perform the compilation
    z3_output = compile_rocq_to_z3(coqc_output)

    # Print the result
    debug_print("--- Rocq Input ---", debug_mode)
    debug_print(coqc_output, debug_mode)
    debug_print("\n--- Z3 SMT-LIB Output ---", debug_mode)
    debug_print(z3_output, debug_mode)
    debug_print("\n--- Z# Solver Result ---", debug_mode)
    solver = Solver() 
    solver.add(parse_smt2_string(z3_output))

    # Check satisfiability
    result = solver.check()
    print(result)  # should print sat/unsat
    if result == sat:
        print(solver.model())

main()