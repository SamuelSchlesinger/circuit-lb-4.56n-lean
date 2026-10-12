# circuit-lb-4.56-lean

Lean 4 proofs of circuit lower bounds from graph layouts.

**Result.** Let `U` be a finite alphabet with at least two symbols and `S_n` a subset
of `U^n` that is `K_n`-rectangle-free, with `log K_n = o(n)` and
`log |S_n| >= n log |U| - o(n)`. For every `epsilon > 0` and all large `n`, every
circuit of fan-in at most two deciding `S_n` has more than `(L - epsilon)n` gates
of positive arity, where

```
L = 1 + pi / (3 * arccos((1 + 2 * sqrt(2)) / 4)) = 4.5624977...
```

A rectangle for a cut `X` of the coordinates is a product `A × B` of a set `A ⊆ U^X` of
assignments to `X` and a set `B ⊆ U^{X^c}` of assignments to the rest. `S_n` is
`K_n`-rectangle-free when every rectangle inside `S_n`, for every cut, has a side with fewer
than `K_n` elements. The basis is arbitrary, fan-out is unbounded, and constants are free. The
theorem assumes such a family; its construction is not formalized here.

An explicit family comes from Xin Li's one-bit extractor `Ext_n` for the sum of two independent
sources ([Li, FOCS 2023](https://eccc.weizmann.ac.il/report/2023/023/)). Choose a fixed extractor
error `delta < 1/2`; Li's theorem gives a constant `c > 1` and an extractor for sources of
min-entropy at least `c log_2 n`. Set `k_n = ceil(c log_2 n)`, take
`S_n = Ext_n^{-1}(0)` over `U = {0, 1}`, and set `K_n = 2^{k_n} = poly(n)`. Zero-padding
assignments on the two sides of a coordinate cut turns the rectangle into sums of two flat
sources. If both sides had at least `K_n` elements while the rectangle lay inside `S_n`, the
extractor output would be constant, at statistical distance `1/2` from uniform, contradicting
`delta < 1/2`. Applying the extractor guarantee to two uniform sources also shows that `S_n`
has constant density.

**Average case.** Let `S_n` instead have density within `b_n` of `1/2` on every rectangle with
both sides of size at least `K_n`. For every `epsilon > 0` there is a `gamma > 0`, uniform over
the alphabet and all admissible families, such that every circuit of fan-in at most two with at
most `(L - epsilon)n` gates of positive arity agrees with `S_n` on at most a
`1/2 + b_n + exp(-gamma n)` fraction of inputs. A one-bit extractor for sumsets with error
`b_n` supplies such sets.

[Statement.lean](Statement.lean) defines both claims using CSLib's circuit model.
[Main.lean](Main.lean) proves each with three coefficients:

- `lowerBound_gaussian`, `averageCase_gaussian`: the exact coefficient above.
- `lowerBound_456`, `averageCase_456`: `114/25 = 4.56`, with a checked numerical inequality.
- `lowerBound_four`, `averageCase_four`: `4`, by a separate vertex-score layout argument.

Build with the pinned toolchain and dependencies:

```sh
lake exe cache get
lake build --wfail
```

The build checks all six proofs against exactly `propext`, `Classical.choice`, and
`Quot.sound`, with warnings treated as errors. The CI then exports the dependency cone of the
six theorems and re-checks it with the external checkers bundled with the toolchain,
including the verified checkers `con-leche` and `con-ron`:

```sh
lake env leanexport Main -- Proofs.lowerBound_gaussian Proofs.lowerBound_456 Proofs.lowerBound_four \
  Proofs.averageCase_gaussian Proofs.averageCase_456 Proofs.averageCase_four > cone.ndjson
lake check --from-export cone.ndjson --paranoid
```

For the argument, start at [LowerBound](Proofs/LowerBound.lean):
[Compiler](Proofs/Compiler.lean) turns circuits into constraint networks,
[Network](Proofs/Network.lean) turns a layout of a network into a read-once branching program
with one layer per cut (unambiguous for compiled circuits),
[BranchingProgram](Proofs/BranchingProgram.lean) shows that such programs for rectangle-free
sets are large, which forces wide cuts, and [Layouts](Proofs/Layouts.lean) supplies the two
graph bounds. [AverageCase](Proofs/AverageCase.lean) peels large rectangles off the programs of
a circuit and its complement to bound agreement. Module comments explain the individual steps.

Mathematical work by Sam Schlesinger, Ryan Williams, and Sam McGuire.
Uses Lean, Mathlib, and CSLib. [Apache 2.0](LICENSE).

## AI Disclosure

Anthropic's Claude Code and OpenAI's Codex were used to implement this formalization. The statements
have been revised by hand and much of the documentation rewritten by Sam Schlesinger.
