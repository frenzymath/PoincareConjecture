import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Terminal.TerminalVolume
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.BoundedDistance
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.Assembly.LongSlabService
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.Noncollapse.SourceNoncollapsePackage
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Universe
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Predecessors

local macro "P.m04.local_derivative_estimates_small" : term =>
  `(PoincareMT.RicciFlowCurvatureTheory.local_derivative_estimates_small
    (PoincareMT.RicciFlowCurvatureTheory.toCalculus $(Lean.mkIdent `P.m04)))

/-!
# Long controls to generalized convergence

The finite-slab service is the geometric part of the long branch.  This
adapter supplies the remaining common inputs: M04's Type-0 derivative
estimates and the terminal-volume lower bound obtained from the common
controls and a bounded-distance threshold.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- Long controls, a bounded-distance threshold, and the reviewed slab service
feed the checked generalized-flow convergence assembly. -/
theorem exists_long_generalized_convergence_of_controls
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u})
    {epsilon canonicalConstant kappa r₀ mu : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongBlowupControls S epsilon canonicalConstant kappa r₀ mu T₀)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (Hslab : M30LongSlabControlService S kappa r₀ T₀) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) := by
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminal_volume_lower_bound P.m04
      H.toM30CommonBlowupControls hbound
  exact exists_backward_generalizedBlowupConvergence_of_longSlabService
    P.m04.local_derivative_estimates_small hMixed hFlow hSlice S
    H.horizon_pos hrho hv H.balls_compact
    Hslab
    hvolume

/-- The same assembly, retaining the finite-slab source noncollapse witness
alongside the selected generalized convergence. -/
theorem exists_long_generalized_convergence_with_source_noncollapse_of_controls
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u})
    {epsilon canonicalConstant kappa r₀ mu : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongBlowupControls S epsilon canonicalConstant kappa r₀ mu T₀)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (Hslab : M30LongSlabControlService S kappa r₀ T₀) :
    Nonempty (GeneralizedBlowupConvergenceWithSourceNoncollapse
      S kappa r₀ T₀) := by
  obtain ⟨L⟩ := exists_long_generalized_convergence_of_controls
    P hMixed hFlow hSlice S H hbound Hslab
  exact ⟨generalizedConvergenceWithSourceNoncollapse_of_slabService Hslab L⟩

end PoincareMT.M30
