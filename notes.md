
1. Semantics to the transformer rules:
input: packet, state
output: updated packet, updated state.

stream of packets, where state persists across all packets in the stream

distinguish extraction in the packet parser, versus extraction for generating keys in match-action processing

Inductive type: packet -> state -> match-action-rule -> packet -> state -> Prop
defining this as : this proposition holds when under this match-action rule, old packet and state, leads to  a new packet and state.
Think of this as a relation: sets of pairs.
A proposition holds when a particular transition fires:
For a math relation: R(a, b), we would say R belongs to power set (X, X)
In Rocq, we would say: R : X -> X -> Prop

Volume 2 of software foundations on operational semantics.
Volume 1 of SF: inductive propositions chapter, regex matching example.

This gives us semantics for one-match-rule.

Then define yet another proposition for a list of match-action rules:
for the whole transformer, encode a priority logic or non-determinism in list of rules for the transformer.

From there, we go from stream of input packets and input state, to a stream of output packets and output state.

(Can do something similar at the SMT formula level:
AST of formulas and inductive prop for semantics.
Check out source of AliveInLean project.
File with the statement of the main theorem.)