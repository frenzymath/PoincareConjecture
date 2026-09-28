import PoincareConjecture.Proofs.M07
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.NormalCharts

set_option autoImplicit false

namespace PoincareConjecture

theorem pointedRicciFlowCompactness_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0}) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  apply H.pointedRicciFlowCompactness_of_uniform_normalChartCover_bounds
  intro A R ρ a b N hA hρ hρR ha hb I hIcompact hI m
  obtain ⟨B, _, hbound⟩ :=
    H.eventually_normalChartCover_spacetime_jet_bound_of_local_derivative_estimates
      hShi hIcompact hI (N := N) hA hρ hρR ha hb.le m
  exact ⟨B, hbound⟩

end PoincareConjecture
