import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalVolume
import PoincareConjecture.Proofs.M30.Thm11_1.BoundedDistance
import PoincareConjecture.Proofs.M30.Thm11_8.LongSlabService
import PoincareConjecture.Proofs.M30.Thm11_8.SourceNoncollapsePackage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Universe
import PoincareConjecture.Statements.M30Providers

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

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

end PoincareConjecture.M30
