import PoincareConjecture.Proofs.M14.Mathlib.RectanglePartialTangent









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

variable {𝕜 E F E' H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E' H}
  [TopologicalSpace M] [ChartedSpace H M]
  {U : Set E} {C : Set F} {α : E × F → M} {m k : ℕ∞ω}




theorem ContMDiffOn.contMDiffOn_partialTangent_fst_prod
    [IsManifold I 1 M]
    (hα : ContMDiffOn ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I m α (U ×ˢ C))
    (hU : IsOpen U) (hC : UniqueDiffOn 𝕜 C) (v : E) (hkm : k + 1 ≤ m) :
    ContMDiffOn ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I.tangent k
      (fun z => Bundle.TotalSpace.mk' E' (α z)
        (mfderiv (𝓘(𝕜, E)) I (fun r => α (r, z.2)) z.1 v)) (U ×ˢ C) := by
  apply (hα.contMDiffOn_partialTangentWithin_fst_prod hU.uniqueDiffOn hC v hkm).congr
  intro z hz
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hz.1)]
