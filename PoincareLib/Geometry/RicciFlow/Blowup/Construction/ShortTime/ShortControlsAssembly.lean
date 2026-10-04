import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Theory
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Terminal.TerminalVolume
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.FiniteSlab.FiniteGeneralizedConvergence
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Universe
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Predecessors

local macro "P.m04.local_derivative_estimates_small" : term =>
  `(PoincareMT.RicciFlowCurvatureTheory.local_derivative_estimates_small
    (PoincareMT.RicciFlowCurvatureTheory.toCalculus $(Lean.mkIdent `P.m04)))

/-!
# Short controls to a repaired short conclusion

The fixed slab in `ShortControlledBlowupHypotheses` is larger than a smaller
target interval chosen below one normalized unit.  This file records the
bookkeeping that forwards that slab, the terminal-volume event, and the
Type-0 analytic services to the audited finite generalized-convergence
assembly.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- A fixed short controlled slab gives a positive backward convergence
interval after the source-scale terminal-volume estimate is supplied. -/
theorem exists_repaired_short_conclusion_of_controls
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u})
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (Hcommon : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (Hshort : ShortControlledBlowupHypotheses S kappa r₀) :
    Nonempty (RepairedShortControlledBlowupConclusion S) := by
  let T : ℝ := min 1 (Hshort.backward_time / 2)
  let tau : ℝ := T / 2
  have hT : 0 < T := by
    dsimp only [T]
    exact lt_min zero_lt_one (half_pos Hshort.backward_time_pos)
  have hT1 : T ≤ 1 := min_le_left _ _
  have hTback : T < Hshort.backward_time := by
    dsimp only [T]
    exact (min_le_right _ _).trans_lt (by linarith [Hshort.backward_time_pos])
  have htau : 0 < tau := by
    dsimp only [tau]
    exact half_pos hT
  have htauT : tau < T := by
    dsimp only [tau]
    linarith
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminal_volume_lower_bound P.m04 Hcommon hbound
  have hcyl : ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in atTop,
        Nonempty (ControlledBlowupCylinder S k A Hshort.backward_time
          Hshort.curvature_bound eta) := by
    intro A hA eta heta
    exact Hshort.cylinders A hA eta heta
  obtain ⟨hconvergence⟩ := exists_finite_generalizedBlowupConvergence
    P.m04.local_derivative_estimates_small hMixed hFlow hSlice P.m07 S
    htau htauT hT1 hTback hrho hv Hshort.balls_compact hcyl hvolume
  exact ⟨{
    backward_time := tau
    backward_time_pos := htau
    convergence := ⟨hconvergence⟩ }⟩

end PoincareMT.M30
