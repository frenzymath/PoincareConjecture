import Mathlib.Geometry.Manifold.IsManifold.Basic










set_option autoImplicit false

open scoped Manifold ContDiff

namespace ChartedSpace

variable {ι H M : Type*} [TopologicalSpace H] [TopologicalSpace M]



@[instance_reducible]
noncomputable def ofChartCover (c : ι → OpenPartialHomeomorph M H)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source) : ChartedSpace H M where
  atlas := Set.range c
  chartAt x := c (Classical.choose (hcover x))
  mem_chart_source x := Classical.choose_spec (hcover x)
  chart_mem_atlas x := ⟨Classical.choose (hcover x), rfl⟩



theorem hasGroupoid_ofChartCover (c : ι → OpenPartialHomeomorph M H)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source) (G : StructureGroupoid H)
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ G) :
    letI := ofChartCover c hcover
    HasGroupoid M G := by
  let := ofChartCover c hcover
  constructor
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  exact hcompat i j

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]



theorem isManifold_ofChartCover_of_contDiffOn (c : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source) (n : ℕ∞ω)
    (hcompat : ∀ i j, ContDiffOn 𝕜 n ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) :
    letI := ofChartCover c hcover
    IsManifold (𝓘(𝕜, E)) n M := by
  let := ofChartCover c hcover
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa only [mfld_simps] using hcompat i j



theorem isManifold_ofChartCover_of_analyticOnNhd (c : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source) (n : ℕ∞ω)
    (hcompat : ∀ i j, AnalyticOnNhd 𝕜 ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) :
    letI := ofChartCover c hcover
    IsManifold (𝓘(𝕜, E)) n M := by
  apply isManifold_ofChartCover_of_contDiffOn c hcover n
  intro i j
  exact (hcompat i j).contDiffOn ((c i).symm.trans (c j)).open_source.uniqueDiffOn

end ChartedSpace
