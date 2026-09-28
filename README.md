# Poincare Conjecture

This repository contains a Lean 4 and Mathlib formalization of the smooth and
topological Poincare theorems following Morgan and Tian's *Ricci Flow and the
Poincare Conjecture*.

The public endpoint theorems are:

```lean
PoincareConjecture.smoothPoincareSkeleton
PoincareConjecture.topologicalPoincareSkeleton
```

Their propositions are defined in
[`PoincareConjecture/Statement.lean`](PoincareConjecture/Statement.lean), and
the final assembly is in
[`PoincareConjecture/Proofs/Main.lean`](PoincareConjecture/Proofs/Main.lean).
The default build checks every Lean file under `PoincareConjecture`.

## Build

The Lean toolchain, Mathlib revision, Comparator revision, and lean4export
revision are pinned in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

```sh
lake build
lake build @Comparator/comparator @lean4export/lean4export
```

## Comparator

The independent statement interface is in
[`Comparator/Challenge.lean`](Comparator/Challenge.lean). The production
solution is in [`Comparator/Solution.lean`](Comparator/Solution.lean), and
the official comparator configuration is
[`Comparator/config.json`](Comparator/config.json).

Follow the Linux sandbox setup and invocation in
[`Comparator/README.md`](Comparator/README.md). The configuration enables both
Lean's kernel and Nanoda and permits only `propext`, `Classical.choice`, and
`Quot.sound`. Comparator checks the independently stated endpoint types and
their production proofs. The two `sorry` placeholders in `Challenge.lean` are
the statements to be checked; the production proof and `Solution.lean` contain
no placeholders.

## Source

The formal statements are the smooth and topological forms of Morgan--Tian
Corollary 0.2. The development uses the standard three-sphere
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1` as its target.
