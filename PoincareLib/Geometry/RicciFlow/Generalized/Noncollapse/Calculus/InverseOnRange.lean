import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Mathlib/InverseOnRange.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# Smooth inverse on an injective local diffeomorphism's range

The inverse is identified with an actual local inverse on each open
inverse chart. This supplies terminal coordinates in Morgan-Tian Claim
8.8, pp. 174-175, without requiring a charted open-subtype construction.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-21-inverse-on-range.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

/-- The chosen inverse of an injective local diffeomorphism is smooth
on its actual range. This is the inverse-coordinate step used in
Morgan-Tian Claim 8.8, pp. 174-175. -/
theorem IsLocalDiffeomorph.contMDiffOn_invFun_of_injective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {k : WithTop ℕ∞} {f : M → N}
    (hf : IsLocalDiffeomorph I J k f) (hinj : Function.Injective f) :
    ContMDiffOn J I k (Function.invFun f) (Set.range f) := by
  rintro _ ⟨x, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  apply (hf x).localInverse_contMDiffAt.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse.open_source.mem_nhds
    (hf x).localInverse_mem_source] with y hy
  apply hinj
  exact (Function.invFun_eq ⟨(hf x).localInverse y, (hf x).localInverse_right_inv hy⟩).trans
    ((hf x).localInverse_right_inv hy).symm
