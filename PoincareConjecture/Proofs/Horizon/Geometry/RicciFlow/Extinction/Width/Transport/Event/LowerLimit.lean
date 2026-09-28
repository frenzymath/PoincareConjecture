import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.FactorLimit

set_option autoImplicit false

namespace PoincareConjecture


theorem m67_factor_tolerance {v epsilon : ℝ} (hv : 0 ≤ v) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ w : ℝ, v ≤ (1 + eta) ^ 2 * w → v ≤ w + epsilon := by
  let eta := min 1 (epsilon / (4 * (v + 1)))
  have hden : 0 < 4 * (v + 1) := by positivity
  have heta : 0 < eta := lt_min zero_lt_one (div_pos hepsilon hden)
  have hsmall : eta ≤ 1 := min_le_left _ _
  have hbudget : 4 * eta * (v + 1) ≤ epsilon := by
    have := (le_div_iff₀ hden).mp (min_le_right 1 (epsilon / (4 * (v + 1))))
    dsimp [eta]
    nlinarith
  refine ⟨eta, heta, fun w hbound => ?_⟩
  by_cases hlarge : v ≤ w
  · linarith
  have hwv : w ≤ v := (lt_of_not_ge hlarge).le
  have hfactor : 0 < (1 + eta) ^ 2 := sq_pos_of_pos (by linarith)
  have hw : 0 ≤ w := by nlinarith
  have hsquare : eta ^ 2 ≤ eta := by nlinarith
  have hsqw : eta ^ 2 * w ≤ eta * w := mul_le_mul_of_nonneg_right hsquare hw
  have hmul : eta * w ≤ eta * v := mul_le_mul_of_nonneg_left hwv heta.le
  nlinarith



theorem m67_lower_limit_of_factor_bounds
    {T : ℝ} (width : Set.Icc (0 : ℝ) T → ℝ) (s : Set.Icc (0 : ℝ) T)
    (hs : 0 ≤ width s)
    (hfactor : ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Icc (0 : ℝ) T, s.1 - delta < t.1 → t.1 < s.1 →
        width s ≤ (1 + eta) ^ 2 * width t) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Icc (0 : ℝ) T, s.1 - delta < t.1 → t.1 < s.1 →
        width s ≤ width t + epsilon := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, htol⟩ := m67_factor_tolerance hs hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := hfactor eta heta
  exact ⟨delta, hdelta, fun t ht hts => htol (width t) (hbound t ht hts)⟩

end PoincareConjecture
