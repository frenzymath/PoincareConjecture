import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Cell.LipschitzAssembly
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Polygon.CellCompact
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Metric.LipschitzBridge

/-!
# Polygon-cell Lipschitz specialization

For an actual annulus map, continuity on the rectangle already puts every
closed polygon cell in one finite-distance target component.  This removes
that bookkeeping from the cell-level smooth-extension call.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- A continuous annulus map with a smooth cell extension has a Lipschitz bound on that
cell. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453;
project construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_polygon_cell_lipschitz_of_extension
    (g : RiemannianMetric n M) {f F : LoopPlane → M}
    {N : ℕ} (hN : 0 < N) (j : Fin N)
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hF : ∀ x ∈ m64PolygonCellSet j,
      ContMDiffAt (𝓡 2) (𝓡 n) 1 F x)
    (hEq : EqOn f F (m64PolygonCellSet j)) :
    ∃ K : ℝ≥0, ∀ x ∈ m64PolygonCellSet j, ∀ y ∈ m64PolygonCellSet j,
      g.edist (f x) (f y) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖x - y‖ := by
  let S := m64PolygonCellSet j
  have hsub : S ⊆ m64AnnulusDomain :=
    m64PolygonCellSet_subset_annulusDomain hN j
  have hfinite : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≠ (⊤ : ENNReal) := by
    intro x hx y hy
    exact m64AnnulusDomain_edist_ne_top g hcontinuous x (hsub hx) y (hsub hy)
  obtain ⟨K, hK⟩ := m64_lipschitzOn_cell_of_extension g
    (m64PolygonCellSet_isCompact hN j) hfinite hF hEq
  exact ⟨K, hK⟩

end PoincareMT
