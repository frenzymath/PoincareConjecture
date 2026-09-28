import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.PolygonTotalCurvature
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlattenedPolygonLength









set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}




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

end PoincareConjecture
