import Mathlib.Geometry.Manifold.IsManifold.Basic











set_option autoImplicit false

open scoped Manifold ContDiff

namespace Homeomorph

variable {H M N : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [TopologicalSpace N]



theorem pullback_chart_transition (e : M ≃ₜ N) (c d : OpenPartialHomeomorph N H) :
    (e.transOpenPartialHomeomorph c).symm.trans (e.transOpenPartialHomeomorph d) =
      c.symm.trans d := by
  apply OpenPartialHomeomorph.ext
  · intro x
    change d (e (e.symm (c.symm x))) = d (c.symm x)
    rw [e.apply_symm_apply]
  · intro x
    change c (e (e.symm (d.symm x))) = c (d.symm x)
    rw [e.apply_symm_apply]
  · ext x
    change (x ∈ c.target ∧ e (e.symm (c.symm x)) ∈ d.source) ↔
      (x ∈ c.target ∧ c.symm x ∈ d.source)
    rw [e.apply_symm_apply]

variable [ChartedSpace H N]



@[instance_reducible]
def pullbackChartedSpace (e : M ≃ₜ N) : ChartedSpace H M where
  atlas := e.transOpenPartialHomeomorph '' atlas H N
  chartAt x := e.transOpenPartialHomeomorph (chartAt H (e x))
  mem_chart_source x := mem_chart_source H (e x)
  chart_mem_atlas x := ⟨chartAt H (e x), chart_mem_atlas H (e x), rfl⟩



theorem hasGroupoid_pullbackChartedSpace (e : M ≃ₜ N) (G : StructureGroupoid H)
    [HasGroupoid N G] :
    letI := e.pullbackChartedSpace (H := H)
    HasGroupoid M G := by
  let := e.pullbackChartedSpace (H := H)
  constructor
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  rw [e.pullback_chart_transition]
  exact G.compatible hc hd



theorem isManifold_pullbackChartedSpace
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (e : M ≃ₜ N) (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    [IsManifold I n N] :
    letI := e.pullbackChartedSpace (H := H)
    IsManifold I n M := by
  let := e.pullbackChartedSpace (H := H)
  let := e.hasGroupoid_pullbackChartedSpace (contDiffGroupoid n I)
  exact IsManifold.mk' I n M

end Homeomorph
