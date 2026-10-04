# Poincare Conjecture

This repository contains a Lean 4 and Mathlib formalization of the smooth and
topological Poincare theorems following Morgan and Tian's *Ricci Flow and the
Poincare Conjecture*.

The implementation is the subject-organized `PoincareLib`, imported from
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a/PoincareConjecture/PoincareLib).
It replaces the previous chapter- and milestone-organized proof tree.
Use `import PoincareLib` to access its endpoints:

```lean
PoincareMT.smoothPoincareSkeleton
PoincareMT.topologicalPoincareSkeleton
```

Their final assembly is exposed by
[`PoincareLib/Topology/Manifold/Poincare.lean`](PoincareLib/Topology/Manifold/Poincare.lean).
The existing `import PoincareConjecture` entry point remains available with
thin wrappers for its two public theorem names:

```lean
PoincareConjecture.smoothPoincareSkeleton
PoincareConjecture.topologicalPoincareSkeleton
```

Only the Mathlib-only
[`PoincareConjecture/Statement.lean`](PoincareConjecture/Statement.lean) and the
endpoint wrappers in
[`PoincareConjecture/Proofs/Main.lean`](PoincareConjecture/Proofs/Main.lean)
remain under the old module prefix. Both wrappers use the `PoincareLib` proofs.
The default build checks `PoincareLib` and these compatibility modules.
See [MODIFICATIONS.md](MODIFICATIONS.md#poincarelib-import) for the exact source and attribution.

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
`Quot.sound`. Comparator checks the independently stated endpoint types against
the imported `PoincareLib` proofs. The two `sorry` placeholders in `Challenge.lean` are
the statements to be checked; the production proof and `Solution.lean` contain
no placeholders.

## Source

See [NOTICE](NOTICE) and [MODIFICATIONS.md](MODIFICATIONS.md) for upstream
copyright notices, adapted source files, and descriptions of modifications.

The formal statements are the smooth and topological forms of Morgan--Tian
Corollary 0.2. The development uses the standard three-sphere
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1` as its target.
