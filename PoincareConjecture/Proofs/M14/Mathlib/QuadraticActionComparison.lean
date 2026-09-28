import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring










set_option autoImplicit false

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem quadratic_action_remainder_lower_bound
    (B₀ B₁ DBw : E →L[ℝ] E →L[ℝ] ℝ) (v d w : E)
    (V₀ V₁ DVw m K M : ℝ) (hm : 0 < m) (hK : 0 ≤ K) (hv : ‖v‖ ≤ M)
    (hsym : B₁ d v = B₁ v d) (hpos : m * ‖d‖ ^ 2 ≤ B₁ d d)
    (hstep : ‖B₁ - B₀‖ ≤ K * ‖w‖)
    (hrem : ‖B₁ - B₀ - DBw‖ ≤ K * ‖w‖ ^ 2)
    (hV : -(K * ‖w‖ ^ 2) ≤ V₁ - V₀ - DVw) :
    m / 4 * ‖d‖ ^ 2 - (K * M ^ 2 / 2 + K + (K * M) ^ 2 / m) * ‖w‖ ^ 2 ≤
      (B₁ (v + d) (v + d) / 2 + V₁) - (B₀ v v / 2 + V₀) -
        (DBw v v / 2 + B₀ v d + DVw) := by
  have hM : 0 ≤ M := (norm_nonneg v).trans hv
  have hcross : |(B₁ - B₀) v d| ≤ K * M * ‖w‖ * ‖d‖ := by
    calc
      _ = ‖(B₁ - B₀) v d‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B₁ - B₀‖ * ‖v‖ * ‖d‖ := (B₁ - B₀).le_opNorm₂ v d
      _ ≤ (K * ‖w‖) * M * ‖d‖ := by gcongr
      _ = _ := by ring
  have htaylor : |(B₁ - B₀ - DBw) v v| ≤ K * M ^ 2 * ‖w‖ ^ 2 := by
    calc
      _ = ‖(B₁ - B₀ - DBw) v v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B₁ - B₀ - DBw‖ * ‖v‖ * ‖v‖ := (B₁ - B₀ - DBw).le_opNorm₂ v v
      _ ≤ (K * ‖w‖ ^ 2) * M * M := by gcongr
      _ = _ := by ring
  have hyoung : K * M * ‖w‖ * ‖d‖ ≤
      m / 4 * ‖d‖ ^ 2 + (K * M) ^ 2 / m * ‖w‖ ^ 2 := by
    have hcancel : (K * M) ^ 2 / m * m = (K * M) ^ 2 := div_mul_cancel₀ _ hm.ne'
    apply (mul_le_mul_iff_right₀ hm).mp
    nlinarith [sq_nonneg (m / 2 * ‖d‖ - K * M * ‖w‖)]
  have hcrossLower := (abs_le.mp hcross).1
  have htaylorLower := (abs_le.mp htaylor).1
  have hid : (B₁ (v + d) (v + d) / 2 + V₁) - (B₀ v v / 2 + V₀) -
      (DBw v v / 2 + B₀ v d + DVw) =
      B₁ d d / 2 + (B₁ - B₀) v d +
        (B₁ - B₀ - DBw) v v / 2 + (V₁ - V₀ - DVw) := by
    simp only [map_add, add_apply, sub_apply, hsym]
    ring
  rw [hid]
  linarith

end PoincareConjecture.M14
