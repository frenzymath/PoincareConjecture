import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.NormalCharts

set_option autoImplicit false

namespace PoincareConjecture

theorem pointedRicciFlowCompactness
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0}) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  apply H.pointedRicciFlowCompactness_of_uniform_normalChartCover_bounds
  intro A R ρ a b N hA hρ hρR ha hb I hIcompact hI m
  obtain ⟨B, _, hbound⟩ := H.eventually_normalChartCover_spacetime_jet_bound
    hM04 hIcompact hI (N := N) hA hρ hρR ha hb.le m
  exact ⟨B, hbound⟩

theorem pointedRicciFlowCompactness_from_M04
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  exact pointedRicciFlowCompactness H ricciFlowCurvatureTheory.{0}

end PoincareConjecture
