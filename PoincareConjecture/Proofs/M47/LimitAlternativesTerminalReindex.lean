import PoincareConjecture.Proofs.M47.TerminalCommonIntervalFloorScale
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalReindex









set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47



theorem limitAlternatives_terminal_common_reindex
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
    (sigma : ℕ → ℕ) (hsigma : StrictMono sigma) :
    1 ≤ K ∧
      Delta = terminalCommonIntervalDuration S B K ∧
      0 < Delta ∧
      Delta ≤ 1 ∧
      (∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
        ∀ y ∈ (terminalCommonInterval_reindex V sigma hsigma).baseBall k A,
          ((terminalCommonInterval_reindex V sigma hsigma).flow k).scalar
            ⟨((terminalCommonInterval_reindex V sigma hsigma).base k).1, y⟩ ≤
            (2 * K) * (terminalCommonInterval_reindex V sigma hsigma).scale k) ∧
      (∀ k, 0 < r (sigma k)) ∧
      (∀ᶠ k in atTop,
        64 * (2 * Delta + 1) ≤
            (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        B.curvature_threshold ≤
            (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        blowupPinchingThreshold (8 * K) eta ≤
            (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        (r (sigma k))⁻¹ ^ 2 ≤
            (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        0 < (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        0 < ((terminalCommonInterval_reindex V sigma hsigma).scale k *
          (r (sigma k)) ^ 2)⁻¹ ∧
        ((terminalCommonInterval_reindex V sigma hsigma).scale k *
          (r (sigma k)) ^ 2)⁻¹ ≤ 1 ∧
        (r (sigma k))⁻¹ ^ 2 /
            (terminalCommonInterval_reindex V sigma hsigma).scale k =
          ((terminalCommonInterval_reindex V sigma hsigma).scale k *
            (r (sigma k)) ^ 2)⁻¹ ∧
        ((terminalCommonInterval_reindex V sigma hsigma).scale k)⁻¹ =
          ((terminalCommonInterval_reindex V sigma hsigma).scale k *
            (r (sigma k)) ^ 2)⁻¹ * (r (sigma k)) ^ 2) := by
  have hscalar' : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      ∀ y ∈ (terminalCommonInterval_reindex V sigma hsigma).baseBall k A,
        ((terminalCommonInterval_reindex V sigma hsigma).flow k).scalar
          ⟨((terminalCommonInterval_reindex V sigma hsigma).base k).1, y⟩ ≤
          (2 * K) * (terminalCommonInterval_reindex V sigma hsigma).scale k := by
    intro A hA
    filter_upwards [hsigma.tendsto_atTop.eventually (hscalar A hA)] with k hk
    change ∀ y ∈ V.baseBall (sigma k) A,
      (V.flow (sigma k)).scalar ⟨(V.base (sigma k)).1, y⟩ ≤
        (2 * K) * V.scale (sigma k)
    exact hk
  have hr' : ∀ k, 0 < r (sigma k) := fun k => hr (sigma k)
  have hscale' : ∀ᶠ k in atTop,
      64 * (2 * Delta + 1) ≤
          (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        B.curvature_threshold ≤
          (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        blowupPinchingThreshold (8 * K) eta ≤
          (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        (r (sigma k))⁻¹ ^ 2 ≤
          (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        0 < (terminalCommonInterval_reindex V sigma hsigma).scale k ∧
        0 < ((terminalCommonInterval_reindex V sigma hsigma).scale k *
          (r (sigma k)) ^ 2)⁻¹ ∧
        ((terminalCommonInterval_reindex V sigma hsigma).scale k *
          (r (sigma k)) ^ 2)⁻¹ ≤ 1 ∧
        (r (sigma k))⁻¹ ^ 2 /
          (terminalCommonInterval_reindex V sigma hsigma).scale k =
          ((terminalCommonInterval_reindex V sigma hsigma).scale k *
            (r (sigma k)) ^ 2)⁻¹ ∧
        ((terminalCommonInterval_reindex V sigma hsigma).scale k)⁻¹ =
          ((terminalCommonInterval_reindex V sigma hsigma).scale k *
            (r (sigma k)) ^ 2)⁻¹ * (r (sigma k)) ^ 2 := by
    filter_upwards [hsigma.tendsto_atTop.eventually hscale] with k hk
    simpa [terminalCommonInterval_reindex, GeneralizedBlowupSequence.scale] using hk
  exact ⟨hK, hDelta, hDeltaPos, hDeltaLe, hscalar', hr', hscale'⟩

end PoincareConjecture.M47
