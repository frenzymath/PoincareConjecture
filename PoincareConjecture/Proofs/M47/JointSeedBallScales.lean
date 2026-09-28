import PoincareConjecture.Proofs.M47.JointSeedScales










set_option autoImplicit false

namespace PoincareConjecture.M47



theorem jointSeed_ball_scale_budget
    {A C c rho v : ℝ} (hA : 0 < A) (hC : 0 < C) (hrho : 0 < rho) (hv : 0 < v)
    (hc : c ≤ 1 / (64 * A * C)) (hsmall : v ≤ rho ^ 2 / (64 * A)) :
    0 < max (rho⁻¹ ^ 2) (C * c / v) ∧
      A * max (rho⁻¹ ^ 2) (C * c / v) * v ≤ 1 / 64 := by
  obtain ⟨hpos, hbudget⟩ := jointSeed_worldline_scale_budget (A := 16 * A)
    (by positivity) hC hrho hv
    (by convert hc using 1; ring) (by convert hsmall using 1; ring)
  exact ⟨hpos, by nlinarith⟩



theorem jointSeed_birth_radius_lt_gradient_radius
    {A B L a v : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hL : 0 < L)
    (ha : 0 < a) (hav : a ≤ v) (hbudget : A * L * v ≤ 1 / 64) :
    0 < Real.sqrt a / (4 * A * B) ∧
      Real.sqrt a / (4 * A * B) < (Real.sqrt (2 * L))⁻¹ / (8 * A) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hv : 0 < v := ha.trans_le hav
  have hLa : L * a ≤ 1 / 64 := by
    calc
      L * a ≤ L * v := mul_le_mul_of_nonneg_left hav hL.le
      _ ≤ A * L * v := by nlinarith [mul_nonneg hL.le hv.le]
      _ ≤ 1 / 64 := hbudget
  have hsqa := Real.sq_sqrt ha.le
  have hsql := Real.sq_sqrt (by positivity : 0 ≤ 2 * L)
  have hroot : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.2 (by positivity)
  have hproduct : 2 * Real.sqrt a * Real.sqrt (2 * L) < B := by
    have hnonneg : 0 ≤ 2 * Real.sqrt a * Real.sqrt (2 * L) := by positivity
    have hsquare : (2 * Real.sqrt a * Real.sqrt (2 * L)) ^ 2 = 8 * a * L := by
      calc
        _ = 4 * (Real.sqrt a) ^ 2 * (Real.sqrt (2 * L)) ^ 2 := by ring
        _ = _ := by rw [hsqa, hsql]; ring
    nlinarith [sq_nonneg (B - 1)]
  refine ⟨by positivity, ?_⟩
  apply (div_lt_iff₀ (by positivity : 0 < 4 * A * B)).2
  have hid : ((Real.sqrt (2 * L))⁻¹ / (8 * A)) * (4 * A * B) =
      B / (2 * Real.sqrt (2 * L)) := by
    field_simp
    ring
  rw [hid]
  apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 * L))).2
  nlinarith

end PoincareConjecture.M47
