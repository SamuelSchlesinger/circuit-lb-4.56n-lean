/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Compiler.Shape
public import Proofs.Compiler.Counting

/-!
# Compiling a circuit into a constraint network

Fix a straight-line program `p` over any signature, *output* wires `out o` indexed by a finite
type `O`, an interpretation `I` of the signature in an alphabet `U`, and for each output a set
`Acc o ⊆ U` of *accepting* values. We build a constraint network whose accepted inputs are
exactly those on which every output `o` lies in `Acc o`. A circuit deciding a set has one output;
a circuit computing a function accepts every value at each of its outputs.

Only the *reachable* wires matter: the outputs and, recursively, the arguments of reachable
gates. We call them *signals*. A signal is *consumed* by each argument slot of a reachable gate
that reads it, and each output is also consumed by its own *output vertex*. A circuit has
unbounded fan-out, but a bounded-degree network cannot give a signal one edge per consumer. So
each signal `w` with consumers `c₀, c₁, ...` is routed through a chain of *junctions*
`j₀, j₁, ...`, one per consumer:

```
  w --- j0 --- j1 --- j2 --- ...
        |      |      |
        c0     c1     c2
```

Each junction has one *feed* edge from its predecessor in the chain (the signal itself for
`j₀`) and one *deliver* edge to its consumer. The constraints are:

* a signal vertex for the input `x_i` reads `x_i` and puts it on its outgoing edge;
* a signal vertex for a gate `g` puts `g` applied to its incoming argument edges on its
  outgoing edge;
* a junction puts its incoming value on both of its outgoing edges;
* the output vertex of `o` requires its incoming value to lie in `Acc o`.

Every vertex has degree at most `r + 1` when the gates have fan-in at most `r ≥ 2`; for fan-in
two the graph is subcubic. The network records gates as *relations*: it never evaluates
anything, and the constraint of a gate does not care which of its edges a layout reaches first.

**Exactness** (`accepted_network`). The values of a run of the program satisfy the network.
Conversely, in a satisfying assignment the junction constraints force all edges of a signal to
carry one value, and the gate constraints, read in program order, force that value to be the
signal's value in the run (`eq_trace`). So the satisfying assignment, if any, is unique, and
along any layout the read-once branching program of the network (`Proofs.Network.branchingProgram`)
is unambiguous (`unambiguous_branchingProgram`).

**Counting.** With `C` consumers, `W` signals, and `|O|` outputs, the network has `2C` edges and
`W + C + |O|` vertices. When the network is connected, its cycle rank is
`C - W - |O| + 1`, the number of slots minus the number of signals plus one. A gate of arity
`k` has `k` slots, so it contributes `k - 1` to the cycle rank, and a reachable input
contributes `-1`. Hence the cycle rank is at most `(r - 1) s + 1 - m` for `s` gates of fan-in
at most `r` and `m` reachable inputs. If all gates are binary and reachable and there are no
constants, the rank is exactly `s + 1 - m`, compared with zero for a read-once binary formula
on `m` distinct inputs: sharing creates cycles. Gates of arity zero, the constants, only lower
the cycle rank, so the count charges only the *inner* gates, those of positive arity.

## Reading order

* `Proofs.Compiler.Basic`: signals, consumers, junctions, vertices, and edges.
* `Proofs.Compiler.Network`: local constraints and exactness.
* `Proofs.Compiler.Shape`: degrees and connectivity.
* `Proofs.Compiler.Counting`: inputs, gates, vertices, edges, and cycle rank.

## Main definitions

* `Proofs.Compiler.network p out I Acc`: the constraint network of a program.

## Main results

* `Proofs.Compiler.accepted_network`, `Proofs.Compiler.eq_trace`: exactness.
* `Proofs.Compiler.unambiguous_branchingProgram`: the branching program of every layout is
  unambiguous.
* `Proofs.Compiler.connected_of_upstream`, `Proofs.Compiler.connected`: the graph is connected
  when some wire is upstream of every output, in particular when `O` is a subsingleton.
* `Proofs.Compiler.maxDegreeLE`: for fan-in at most `r ≥ 2`, the degrees are at most `r + 1`.
* `Proofs.Compiler.cycleRank_add_ncard_read_le`: for a connected compiler graph, the cycle rank
  plus `|read|` is at most `(r - 1) s + 1`, where `s` counts the inner gates.
* `Proofs.Compiler.card_vertex_le`: there are at most `2 r s + 3 |O|` vertices.
-/
