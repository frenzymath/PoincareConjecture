import PoincareConjecture.Proofs.M47.LimitAlternativesTerminalCommon
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSlabs

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitAlternatives_common_slab_of_cap_exclusion
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (V : GeneralizedBlowupSequence.{u})
    {K Delta eta : ℝ}
    (hK : 1 ≤ K)
    (hDelta : Delta = terminalCommonIntervalDuration S B K)
    (hDeltaPos : 0 < Delta) (hDeltaLe : Delta ≤ 1)
    (hscalar : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, ∀ y ∈ V.baseBall k A,
      (V.flow k).scalar ⟨(V.base k).1, y⟩ ≤ (2 * K) * V.scale k)
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hthreshold : ∀ k, (r k)⁻¹ ^ 2 ≤ V.scale k)
    (hscale : ∀ᶠ k in atTop,
      64 * (2 * Delta + 1) ≤ V.scale k ∧
      B.curvature_threshold ≤ V.scale k ∧
      blowupPinchingThreshold (8 * K) eta ≤ V.scale k ∧
      (r k)⁻¹ ^ 2 ≤ V.scale k ∧
      0 < V.scale k ∧
      0 < (V.scale k * (r k) ^ 2)⁻¹ ∧
      (V.scale k * (r k) ^ 2)⁻¹ ≤ 1 ∧
      (r k)⁻¹ ^ 2 / V.scale k = (V.scale k * (r k) ^ 2)⁻¹ ∧
      (V.scale k)⁻¹ = (V.scale k * (r k) ^ 2)⁻¹ * (r k) ^ 2)
    {Cap : ℝ → ℝ → ℕ → Prop}
    (hchoice : ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k in atTop,
        Nonempty (ControlledBlowupCylinder V k A Delta
          (13 * max (8 * K) 1) eta) ∨ Cap A eta k)
    (hnoCap : ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k in atTop, ¬ Cap A eta k) :
    1 ≤ K ∧
      Delta = terminalCommonIntervalDuration S B K ∧
      0 < Delta ∧
      Delta ≤ 1 ∧
      (∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, ∀ y ∈ V.baseBall k A,
        (V.flow k).scalar ⟨(V.base k).1, y⟩ ≤ (2 * K) * V.scale k) ∧
      (∀ k, 0 < r k) ∧
      (∀ k, (r k)⁻¹ ^ 2 ≤ V.scale k) ∧
      (∀ᶠ k in atTop,
        64 * (2 * Delta + 1) ≤ V.scale k ∧
        B.curvature_threshold ≤ V.scale k ∧
        blowupPinchingThreshold (8 * K) eta ≤ V.scale k ∧
        (r k)⁻¹ ^ 2 ≤ V.scale k ∧
        0 < V.scale k ∧
        0 < (V.scale k * (r k) ^ 2)⁻¹ ∧
        (V.scale k * (r k) ^ 2)⁻¹ ≤ 1 ∧
        (r k)⁻¹ ^ 2 / V.scale k = (V.scale k * (r k) ^ 2)⁻¹ ∧
        (V.scale k)⁻¹ = (V.scale k * (r k) ^ 2)⁻¹ * (r k) ^ 2) ∧
      TerminalCommonIntervalSlab V Delta := by
  have hslab : TerminalCommonIntervalSlab V Delta := by
    refine ⟨13 * max (8 * K) 1, ?_, ?_⟩
    · positivity
    · intro A hA eta heta
      filter_upwards [hchoice A hA eta heta, hnoCap A hA eta heta] with k hk hnot
      exact hk.resolve_right hnot
  exact ⟨hK, hDelta, hDeltaPos, hDeltaLe, hscalar, hr, hthreshold, hscale, hslab⟩

end PoincareConjecture.M47
