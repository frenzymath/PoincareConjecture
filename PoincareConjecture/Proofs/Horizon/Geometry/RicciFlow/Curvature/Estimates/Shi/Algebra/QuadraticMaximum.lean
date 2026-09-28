import Mathlib.Tactic













set_option autoImplicit false

namespace PoincareConjecture.RicciFlowAnalysis

theorem weighted_cutoff_quadratic_bound
    {c b d L G Θ τ W η : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (hG : 0 ≤ G) (hΘ : 0 ≤ Θ) (hτ : 0 < τ) (hτΘ : τ ≤ Θ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hW : 0 ≤ W)
    (hineq : c * (W - η * b) ^ 2 ≤ d * η ^ 2 + τ * (L + 2 * G) * W) :
    W ≤ max (2 * b) (max 1 (4 * (d + Θ * (L + 2 * G)) / c)) := by
  by_contra hnot
  have hmax : max (2 * b) (max 1 (4 * (d + Θ * (L + 2 * G)) / c)) < W :=
    lt_of_not_ge hnot
  have hW1 : 1 < W := lt_of_le_of_lt
    ((le_max_left (1 : ℝ) _).trans (le_max_right _ _)) hmax
  have hWpos : 0 < W := lt_trans (by positivity) hW1
  have h2b : 2 * b < W := lt_of_le_of_lt (le_max_left _ _) hmax
  have hηb : η * b ≤ b := by
    have := mul_le_mul_of_nonneg_right hη1 hb
    simpa using this
  have hhalf : W / 2 < W - η * b := by
    nlinarith
  have hsq : W ^ 2 / 4 < (W - η * b) ^ 2 := by
    nlinarith [sq_nonneg (W / 2), sq_nonneg (W - η * b)]
  have hA : 0 ≤ L + 2 * G := by linarith
  have hηsq : η ^ 2 ≤ 1 := by nlinarith
  have hta : τ * (L + 2 * G) ≤ Θ * (L + 2 * G) :=
    mul_le_mul_of_nonneg_right hτΘ hA
  have hfirst : d * η ^ 2 ≤ d := by
    have h := mul_le_mul_of_nonneg_left hηsq hd
    simpa using h
  have hsecond : τ * (L + 2 * G) * W ≤
      Θ * (L + 2 * G) * W :=
    mul_le_mul_of_nonneg_right hta hWpos.le
  have hRhs : d * η ^ 2 + τ * (L + 2 * G) * W ≤
      (d + Θ * (L + 2 * G)) * W := by
    calc
      d * η ^ 2 + τ * (L + 2 * G) * W ≤
          d + Θ * (L + 2 * G) * W := add_le_add hfirst hsecond
      _ ≤ (d + Θ * (L + 2 * G)) * W := by
        nlinarith
  have hleft : c * W ^ 2 / 4 < c * (W - η * b) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_left hsq hc
    nlinarith
  have hX : 4 * (d + Θ * (L + 2 * G)) / c < W :=
    have hXle : 4 * (d + Θ * (L + 2 * G)) / c ≤
        max (2 * b) (max 1 (4 * (d + Θ * (L + 2 * G)) / c)) :=
      (le_max_right (1 : ℝ) _).trans (le_max_right (2 * b) _)
    lt_of_le_of_lt hXle hmax
  have hquad : c * W ^ 2 / 4 <
      (d + Θ * (L + 2 * G)) * W :=
    lt_of_lt_of_le hleft (hineq.trans hRhs)
  have hcW : 4 * (d + Θ * (L + 2 * G)) < c * W :=
    by simpa [mul_comm] using (div_lt_iff₀ hc).mp hX
  have hmul := mul_lt_mul_of_pos_right hcW hWpos
  have hcontra : (d + Θ * (L + 2 * G)) * W < c * W ^ 2 / 4 := by
    nlinarith [hmul]
  exact (lt_asymm hquad hcontra)

end PoincareConjecture.RicciFlowAnalysis
