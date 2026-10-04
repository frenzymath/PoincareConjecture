import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.AtlasOfCover
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Assembling the coordinate output of Cairns' construction

Smooth or analytic transition maps for covering Euclidean coordinate domains
give a compatible smooth atlas on the original topological carrier.
This is the atlas assembly step of Cairns 1940, Section 9, p. 806, and
Theorem III, pp. 797, 807; see M76 derivation 05. The construction of
transversal planes and the compatible coordinate family remains separate.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.M76

variable {ι M : Type*} [TopologicalSpace M]

/-- The smooth coordinates produced in Cairns Section 9, p. 806, suffice for
a smooth replacement atlas. Coverage and regularity are explicit premises;
see M76 derivation 05. -/
theorem exists_smooth_atlas_of_coordinates
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, ContDiffOn ℝ ∞ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) :
    ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := a; IsManifold (𝓡 3) ∞ M :=
  ⟨ChartedSpace.ofChartCover c hcover,
    ChartedSpace.isManifold_ofChartCover_of_contDiffOn c hcover ∞ hcompat⟩

/-- Cairns' analytic coordinate output also supplies the required smooth
replacement atlas. See Theorem III, p. 797, and M76 derivation 05. -/
theorem exists_smooth_atlas_of_analytic_coordinates
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, AnalyticOnNhd ℝ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) :
    ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := a; IsManifold (𝓡 3) ∞ M :=
  ⟨ChartedSpace.ofChartCover c hcover,
    ChartedSpace.isManifold_ofChartCover_of_analyticOnNhd c hcover ∞ hcompat⟩

end PoincareMT.M76
