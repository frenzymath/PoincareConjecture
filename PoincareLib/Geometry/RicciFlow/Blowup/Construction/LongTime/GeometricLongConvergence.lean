import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.BackwardLimit.BackwardGeneralizedConvergence
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Universe
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Predecessors

local macro "P.m04.local_derivative_estimates_small" : term =>
  `(PoincareMT.RicciFlowCurvatureTheory.local_derivative_estimates_small
    (PoincareMT.RicciFlowCurvatureTheory.toCalculus $(Lean.mkIdent `P.m04)))

/-!
# Geometric controls to full-horizon convergence

The geometric branch has the same controlled cylinders and terminal-volume
input as the expanding-time assembly.  Once the three explicit lower analytic
services are available, the existing Type-0 assembly supplies the generalized
convergence on the whole backward horizon.

The services are kept as arguments because their reviewed M28 suppliers are
not part of the frozen M30 predecessor record.  This adapter is therefore
ready for the lower-library promotion without asserting an unprovided
analytic theorem.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- Geometric long controls feed the checked expanding-time assembly once the
within-flow, bilinear-flow, and spatial-slice services are supplied. -/
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

end PoincareMT.M30
