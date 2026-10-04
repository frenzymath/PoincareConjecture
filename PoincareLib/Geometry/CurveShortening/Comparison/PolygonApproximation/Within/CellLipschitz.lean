import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Metric.LipschitzBridge

/-!
# Within-cell metric Lipschitz transfer

The polygon map is only smooth after restricting to one cell.  This file
records the elementary transfer from a smooth extension to the actual map on
that cell.  It is the local interface consumed by the compact globalization
bridge; the geometric construction of the extensions remains with the
polygon/interpolator supplier.

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

/-- Restrict a smooth extension's local metric Lipschitz bound to the actual cell map.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_lipschitzOn_nhdsWithin_of_extension
    (g : RiemannianMetric n M) {f F : LoopPlane → M} {S : Set LoopPlane}
    {x : LoopPlane}
    (hF : ContMDiffAt (𝓡 2) (𝓡 n) 1 F x)
    (hEq : EqOn f F S) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, ∀ y ∈ U ∩ S, ∀ z ∈ U ∩ S,
      g.edist (f y) (f z) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
  obtain ⟨K, U, hU, hK⟩ :=
    m64_lipschitzOn_nhds_of_contMDiffAt g hF
  refine ⟨K, U, hU, ?_⟩
  intro y hy z hz
  rw [hEq hy.2, hEq hz.2]
  exact hK y hy.1 z hz.1

end PoincareMT
