#!/bin/bash
# Lower each .p4 here with the rocq extension and check the equivalences that
# are supposed to hold between them.
#
# The oracle is EqCheck, not a concrete run: run_net seeds memory regions but
# not the read tape, so any program with a parser rejects under it.  That is a
# better test anyway -- "these two lowerings agree for EVERY 32-bit input" is
# what the checker answers, and it is the property the lowering has to have.
#
# Usage: translation/tests/run.sh        (from anywhere)

set -u

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
rocq="$root/translation/p4c/build/rocq"
eqcheck="$root/_build/default/extracted_code/EqCheck.exe"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

fail=0

for tool in "$rocq" "$eqcheck"; do
  if [ ! -x "$tool" ]; then
    echo "missing $tool" >&2
    echo "  build it: (cd translation/p4c/build && make rocq)   /   (cd $root && make && dune build)" >&2
    exit 2
  fi
done

# Lower one program; its stderr carries the field table, which is a comment
# stream and not part of the s-expression.
lower() {
  local name=$1
  # Extra compiler flags, for a program whose architecture is not v1model:
  # a .flags sidecar, with @ROOT@ standing for the repository root.
  local flags=""
  if [ -f "$here/$name.flags" ]; then
    flags=$(sed "s|@ROOT@|$root|g" "$here/$name.flags" | tr '\n' ' ')
  fi
  # A table the P4 source does not populate itself takes its entries from an
  # .entries sidecar; see --table-entries.  The two calls are spelled out
  # rather than built as an array, because an empty array under `set -u` is an
  # unbound variable in the bash macOS ships.
  local ok=0
  if [ -f "$here/$name.entries" ]; then
    # shellcheck disable=SC2086
    "$rocq" $flags --table-entries "$here/$name.entries" "$here/$name.p4" \
        2>"$work/$name.log" >"$work/$name.ir" || ok=1
  else
    # shellcheck disable=SC2086
    "$rocq" $flags "$here/$name.p4" 2>"$work/$name.log" >"$work/$name.ir" || ok=1
  fi
  if [ $ok -ne 0 ]; then
    echo "FAIL  $name did not lower"; sed 's/^/        /' "$work/$name.log"; fail=1
    return 1
  fi
  return 0
}

# check <expected> <a> <b>: the verdict EqCheck must give for the pair.
check() {
  local want=$1 a=$2 b=$3
  lower "$a" || return
  lower "$b" || return
  local got
  got=$("$eqcheck" --net "$work/$a.ir" "$work/$b.ir" 2>&1 | tail -1)
  if [ "$got" = "$want" ]; then
    printf 'ok    %-16s %-16s %s\n' "$a" "$b" "$got"
  else
    printf 'FAIL  %-16s %-16s got %-18s want %s\n' "$a" "$b" "$got" "$want"
    fail=1
  fi
}

# A rotate is slices and a concatenation, or shifts and an or.  Both have to
# lower to the same function of the input -- this is the whole of the
# expression lowering (Slice, Concat, Shl, Shr, the casts between containers)
# checked against itself.
check "Equivalent"     rotl5_concat rotl5_shift

# ... and the same pair with one rotated by six instead, so that a lowering
# which quietly produced a constant would not pass the line above.
check "Not Equivalent" rotl5_concat rotl6_shift

# Fridge's expected-ACK, once as the source writes it -- six steps threaded
# through metadata, under a nested if/else and an isValid -- and once as a
# single expression.  Between them this covers predication (the guard on each
# module), isValid derived from the parser's select, metadata as Headers, and
# the zero-init prologue.
check "Equivalent"     fridge_eack  fridge_eack_direct

# ... with the IPv4 header length scaled by two rather than four, which is the
# control for the line above.
check "Not Equivalent" fridge_eack  fridge_eack_wrong

# A table is a match-action unit and lowers to one module of ordered rules.
# Against the same dispatch written as an if/else chain, this checks the entry
# ordering, the default action, and binding an action's parameter -- the table
# passes set(0xdeadbeef) where the chain assigns the literal.
check "Equivalent"     table_const  table_ifchain

# The same table populated from --table-entries instead of from the source.
check "Equivalent"     table_const  table_supplied

# ... with two entries swapped, as the control for both lines above.
check "Not Equivalent" table_const  table_wrong

# The Tofino-native path: intrinsic metadata as Headers, pkt.advance, and a
# sub-parser inlined by the frontend.  The arithmetic is the same rotate as
# above, so a difference here is the architecture handling and nothing else.
check "Equivalent"     tna_rotl_concat tna_rotl_shift

# A header the parser reaches two ways -- basic_tunnel's shape -- so its
# validity is a disjunction of parse paths.  Checking the DERIVED predicate
# against the same condition written out by hand is what pins the parser walk:
# the two agree for every input, or the checker says where they do not.  The
# hand-written side also exercises `||` in a control condition.
check "Equivalent"     valid_merge  valid_merge_spelled

# ... with the tunnelled protocol wrong in the hand-written one.
check "Not Equivalent" valid_merge  valid_merge_wrong

# `exit` ends the control, so what follows it must not run.  Against the same
# control flow written as an if/else, with a no-exit version as the control.
check "Equivalent"     exit_skips   exit_ifelse
check "Not Equivalent" exit_skips   exit_missing

# Assigning to a bit slice is a read-modify-write of the whole variable, since
# an HdrOp replaces a Header's value rather than part of it.  Two slice writes
# building a halfword swap, against the same swap as one expression.
check "Equivalent"     slice_assign slice_assign_whole
check "Not Equivalent" slice_assign slice_assign_wrong

# A deparser whose body is a table apply -- the shape p4c's midend leaves after
# SynthesizeActions and MoveActionsToTables -- against the same deparser written
# as bare emits.  The lowering used to walk only a deparser's top-level
# statements and skip what it did not recognise, so the table-dispatched side
# emitted nothing at all and no diagnostic said so.  The _wrong control is what
# stops a regression from passing by making BOTH sides emit nothing.
check "Equivalent"     deparse_direct deparse_table
check "Not Equivalent" deparse_direct deparse_table_wrong

# ConQuest's baseline forwarding program, used as-is from
# Princeton-Cabernet/p4-projects: a Tofino-native program whose ingress routes
# on the top byte of the IPv4 destination.  The variant takes the same byte by
# a shift and a mask instead of a slice; the control routes on the second byte.
# This pair is what showed that a forwarding decision was not observable at all
# until the deparser began emitting the intrinsic metadata a program writes.
check "Equivalent"     conquest_baseline conquest_baseline_alt
check "Not Equivalent" conquest_baseline conquest_baseline_wrong

exit $fail
