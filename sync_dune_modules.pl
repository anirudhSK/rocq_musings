#!/usr/bin/env perl
use strict;
use warnings;

-d 'extracted_code' or die "Run from the project root\n";
my $dune = 'extracted_code/dune';

# Hand-written .ml-only files that belong in extracted_code_lib.
# Everything else without a .mli is an executable or belongs to semantics_tests.
my @manual = qw(CrTypeIF MemSolver Shim Z3Solver);

# Collect module names: .mli basenames + manual list, deduped and sorted.
my %seen;
my @modules = sort grep { !$seen{$_}++ }
    ( (map { /([^\/]+)\.mli$/; $1 } glob('extracted_code/*.mli')),
      @manual );

# Format into wrapped lines with 2-space indent, max 80 chars wide.
my ($indent, $width) = ('  ', 80);
my @lines;
my $line = $indent;
for my $m (@modules) {
    if    ($line eq $indent)                         { $line .= $m }
    elsif (length($line) + 1 + length($m) <= $width) { $line .= " $m" }
    else  { push @lines, $line; $line = "$indent$m" }
}
push @lines, $line if $line ne $indent;
my $formatted = join "\n", @lines;

# Read, patch, write.
open my $fh, '<', $dune or die "Cannot read $dune: $!";
my $text = do { local $/; <$fh> };
close $fh;

# Anchor to the extracted_code_lib stanza, then replace its (modules ...) block.
# Module names contain no parens, so [^)]+ safely matches the whole block.
$text =~ s{
    (\(name \s+ extracted_code_lib\) .*?)  # anchor
    \ \(modules [^)]+ \)                   # existing modules block
}{$1 (modules\n$formatted)}xs
    or die "Could not find (modules ...) in extracted_code_lib stanza\n";

open $fh, '>', $dune or die "Cannot write $dune: $!";
print $fh $text;
close $fh;

printf "Updated %s with %d modules.\n", $dune, scalar @modules;
