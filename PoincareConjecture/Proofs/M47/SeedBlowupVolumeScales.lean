import PoincareConjecture.Proofs.M47.LimitNoncollapseCylinders

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_blowup_test_radius {tau B : ℝ} (htau : 0 < tau) (hB : 0 ≤ B) :
    ∃ rho : ℝ, 0 < rho ∧ rho ^ 2 ≤ tau ∧ B ≤ rho⁻¹ ^ 2 := by
  let rho := min (Real.sqrt tau) (1 / Real.sqrt (B + 1))
  have hroot : 0 < Real.sqrt (B + 1) := Real.sqrt_pos.mpr (by linarith)
  have hrho : 0 < rho := lt_min (Real.sqrt_pos.mpr htau) (div_pos zero_lt_one hroot)
  have htime : rho ^ 2 ≤ tau := by
    have hle : rho ≤ Real.sqrt tau := min_le_left _ _
    nlinarith [Real.sq_sqrt htau.le, Real.sqrt_nonneg tau]
  have hsmall : rho ≤ 1 / Real.sqrt (B + 1) := min_le_right _ _
  have hinv : Real.sqrt (B + 1) ≤ rho⁻¹ := by
    simpa only [inv_inv] using
      (inv_le_inv₀ (inv_pos.mpr hroot) hrho).mpr (by simpa only [one_div] using hsmall)
  refine ⟨rho, hrho, htime, ?_⟩
  nlinarith [Real.sq_sqrt (show 0 ≤ B + 1 by linarith), sq_nonneg (rho⁻¹)]

theorem seed_blowup_physical_radius_le {rho epsilon Q : ℝ}
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) (hQ : 0 < Q)
    (hlarge : (rho / epsilon) ^ 2 ≤ Q) :
    rho / Real.sqrt Q ≤ epsilon := by
  have hsqrt : rho / epsilon ≤ Real.sqrt Q := by
    have h := Real.sqrt_le_sqrt hlarge
    simpa only [Real.sqrt_sq (div_pos hrho hepsilon).le] using h
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).2
  have h := (div_le_iff₀ hepsilon).mp hsqrt
  nlinarith

theorem seed_blowup_eventually_radius_le {rho epsilon : ℝ}
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) (Q : ℕ → ℝ)
    (hQ : Tendsto Q atTop atTop) :
    ∀ᶠ n in atTop, 0 < Q n ∧ rho / Real.sqrt (Q n) ≤ epsilon := by
  filter_upwards [hQ.eventually (eventually_ge_atTop ((rho / epsilon) ^ 2))] with n hn
  have hpos : 0 < Q n := (sq_pos_of_pos (div_pos hrho hepsilon)).trans_le hn
  exact ⟨hpos, seed_blowup_physical_radius_le hrho hepsilon hpos hn⟩

end PoincareConjecture.Proofs.M47
