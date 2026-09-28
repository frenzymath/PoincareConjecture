import PoincareConjecture.Proofs.M30.Thm11_8.BackwardGeneralizedConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Universe
import PoincareConjecture.Statements.M30Providers

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem exists_geometric_long_generalizedBlowupConvergence
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u}) {T₀ : ℝ≥0∞}
    (H : M30GeometricLongControls S T₀) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) := by
  rcases H.terminal_volume with ⟨rho, v, hrho, hv, hvolume⟩
  exact exists_backward_generalizedBlowupConvergence
    P.m04.local_derivative_estimates_small hMixed hFlow hSlice S
    H.horizon_pos hrho hv H.balls_compact (fun T hT hTT => H.cylinders T hT hTT)
    hvolume

end PoincareConjecture.M30
