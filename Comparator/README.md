# Comparator

The comparator checks the two public Poincare endpoint propositions against an
independent Mathlib-only statement module.

`Challenge.lean` defines the endpoint types with two `sorry` placeholders for
the required proofs. `Solution.lean` imports the Mathlib-only
`PoincareConjecture.Statement` module and the subject-organized
`PoincareLib.Topology.Manifold.Poincare` assembly. It applies
`PoincareMT.smoothPoincareSkeleton` and `PoincareMT.topologicalPoincareSkeleton`
to prove the corresponding declarations. Keeping the public definitions in their
own module prevents proof-library instances from changing statement elaboration.
`config.json` names both
modules, the two theorem targets, and the permitted foundational axioms.

Use Linux with a working user systemd service and install
[Landrun](https://github.com/Zouuup/landrun) and
[Nanoda](https://github.com/ammkrn/nanoda_lib) in `PATH`. Both are required by
this configuration. The Comparator and lean4export revisions are pinned in
the root Lake configuration.

The external tool revisions used for verification are:

- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (0.1.18).
- Nanoda: `079049d584b2aed2b0172218164082f4fc6eede2` (0.4.18).

The parallel Nanoda executable sets `cfg.num_threads = 32` after loading its
configuration when that value is `0`. Its checker library is unchanged. The
stock executable performs the same checks with its default worker count.
Set `COMPARATOR_NANODA` to select an alternative executable; the command
below defaults to `nanoda_bin` in `PATH`.

From the repository root, build the two modules separately from each other and
the tools, then run as an unprivileged user. Use a disk-backed `TMPDIR` with
sufficient free space for the exported environments:

```sh
lake build Challenge Solution @Comparator/comparator @lean4export/lean4export
export TMPDIR="${TMPDIR:-$HOME/.cache/poincare-comparator}"
mkdir -p "$TMPDIR"
export PATH="$PWD/.lake/packages/Comparator/.lake/build/bin:$PWD/.lake/packages/lean4export/.lake/build/bin:$PATH"
export COMPARATOR_NANODA="${COMPARATOR_NANODA:-nanoda_bin}"
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX --working-directory="$PWD" \
  -E PATH -E COMPARATOR_NANODA -E TMPDIR -- lake env comparator Comparator/config.json
```

Success requires `Nanoda kernel accepts the solution`,
`Lean default kernel accepts the solution`, and `Your solution is okay!`.
The sandbox restriction follows the
[pinned upstream instructions](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097).

The import PR has not run a Lean build or Comparator; verification is left to
the reviewer. The source repository's
[earlier verification report](https://github.com/frenzymath/Poincare-Conjecture/blob/432c38f2aa5a30efb13871292d17b4a3309a496a/archive/PoincareConjecture/references/ricci-flow/mapher/integration-verification/README.md)
records a successful run with a small Comparator execution-order patch that
runs Nanoda before parsing the environments, avoiding simultaneous retention of
both kernels' proof representations. The command above uses the pinned stock
driver, which may require more memory. The source's
[hash-checked patch and preparation script](https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a/PoincareConjecture/Comparator)
are available for reviewers needing that memory optimization; both kernel checks,
statement comparison and axiom validation remain required.
