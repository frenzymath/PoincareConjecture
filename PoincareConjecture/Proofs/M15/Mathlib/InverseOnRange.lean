import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

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
