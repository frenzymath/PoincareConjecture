import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph










set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H]
  {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {r : ℕ∞ω}




theorem IsLocalDiffeomorphAt.of_comp_left
    {f : M → N} {g : N → P} {x : M}
    (hgf : IsLocalDiffeomorphAt I K r (g ∘ f) x)
    (hg : IsLocalDiffeomorphAt J K r g (f x))
    (hf : ContinuousAt f x) :
    IsLocalDiffeomorphAt I J r f x := by
  apply (hgf.comp J N hg.localInverse_isLocalDiffeomorphAt).congr_of_eventuallyEq
  exact (hg.localInverse_eventuallyEq_left.comp_tendsto hf).symm

end
