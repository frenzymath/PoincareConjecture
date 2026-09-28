import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover
import Mathlib.Geometry.Manifold.Instances.Real











set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M76

variable {ι M : Type*} [TopologicalSpace M]




theorem exists_smooth_atlas_of_coordinates
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, ContDiffOn ℝ ∞ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) :
    ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := a; IsManifold (𝓡 3) ∞ M :=
  ⟨ChartedSpace.ofChartCover c hcover,
    ChartedSpace.isManifold_ofChartCover_of_contDiffOn c hcover ∞ hcompat⟩



theorem exists_smooth_atlas_of_analytic_coordinates
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, AnalyticOnNhd ℝ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) :
    ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := a; IsManifold (𝓡 3) ∞ M :=
  ⟨ChartedSpace.ofChartCover c hcover,
    ChartedSpace.isManifold_ofChartCover_of_analyticOnNhd c hcover ∞ hcompat⟩

end PoincareConjecture.M76
