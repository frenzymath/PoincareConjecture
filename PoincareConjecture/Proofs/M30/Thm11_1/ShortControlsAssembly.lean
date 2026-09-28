import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Statements.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalVolume
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteGeneralizedConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Universe
import PoincareConjecture.Statements.M30Providers

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

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

end PoincareConjecture.M30
