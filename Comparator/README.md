# Comparator

The comparator checks the two public Poincare endpoint propositions against an
independent Mathlib-only statement module.

`Challenge.lean` defines the endpoint types with two `sorry` placeholders for
the required proofs. `Solution.lean` imports the production
assembly and proves the corresponding declarations. `config.json` names both
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

From the repository root, build the tools and run as an unprivileged user:

```sh
lake build @Comparator/comparator @lean4export/lean4export
export PATH="$PWD/.lake/packages/Comparator/.lake/build/bin:$PWD/.lake/packages/lean4export/.lake/build/bin:$PATH"
export COMPARATOR_NANODA="${COMPARATOR_NANODA:-nanoda_bin}"
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX --working-directory="$PWD" \
  -E PATH -E COMPARATOR_NANODA -- lake env comparator Comparator/config.json
```

Success requires `Nanoda kernel accepts the solution`,
`Lean default kernel accepts the solution`, and `Your solution is okay!`.
The sandbox restriction follows the
[pinned upstream instructions](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097).
