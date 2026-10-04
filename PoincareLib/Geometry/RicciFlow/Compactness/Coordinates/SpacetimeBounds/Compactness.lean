import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bounds
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.NormalCharts

/-! # Pointed Ricci-flow compactness from the supplied curvature theory

The proved metric-jet estimates discharge the normal-chart exhaustion
assembler's remaining analytic hypothesis.
-/

set_option autoImplicit false

namespace PoincareMT

/-- The frozen M07 conclusion needs only the local curvature derivative estimates. -/
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

/-- The frozen M07 conclusion from its original hypotheses and supplied M04. -/
theorem pointedRicciFlowCompactness
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0}) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) :=
  pointedRicciFlowCompactness_of_local_derivative_estimates H hM04.local_derivative_estimates

end PoincareMT
