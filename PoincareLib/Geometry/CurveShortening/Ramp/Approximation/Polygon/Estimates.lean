import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Polygon.TotalCurvature
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Flattened.PolygonLength

/-!
# Complete estimates for the supplied geodesic polygon

Assemble the actual flattened polygon's geometry and its canonical ramp's
geometry, length and total turning in the frozen record. Claim 19.22,
MT2007 pp. 452-453; see `2026-09-21-actual-polygon-turning.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}

/-- Every supplied geodesic polygon with a positive side count satisfies
all twelve frozen flattened-polygon and canonical-graph estimates.
Claim 19.22, MT2007 pp. 452-453. -/
theorem m63PolygonEstimates (P : M62.CircleProductData F circumference)
    (t : ℝ) {N : ℕ} (polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N)
    (hN : 0 < N) : M63PolygonEstimates P t N polygon := by
  have hperiod := m63FlattenedPolygon_periodic polygon hN
  have hsmooth := m63FlattenedPolygon_smooth polygon hN
  have hdiff := hsmooth.mdifferentiable (by simp)
  exact
    { flattened_periodic := hperiod
      flattened_smooth := hsmooth
      flattened_length := m63FlattenedPolygon_length F t polygon hN
      flattened_cell_velocity := fun j _ hs =>
        m63FlattenedPolygon_cell_velocity polygon hN j hs
      flattened_cell_speed := fun j _ hs => m63FlattenedPolygon_cell_speed polygon hN j hs
      graph_periodic := M63.canonicalRamp_periodic P hperiod
      graph_smooth := M63.canonicalRamp_contMDiff P le_rfl hsmooth
      graph_ramp := M63.canonicalRamp_isRamp P hdiff t
      graph_velocity := fun x => M63.canonicalRamp_velocity P (hdiff x)
      graph_degree_one := M63.canonicalRamp_degree_one P _
      graph_length := M63.canonicalRamp_length_le P (hsmooth.of_le (by simp)) t
      graph_total_curvature := m63FlattenedPolygon_graph_totalCurvature P t polygon hN }

end PoincareMT
