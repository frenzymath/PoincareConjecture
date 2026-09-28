import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Model

set_option autoImplicit false

open Set

namespace PoincareConjecture.RiemannianMetric

private lemma sinh_le_mul_exp (t : ℝ) : Real.sinh t ≤ t * Real.exp t := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-2 * t)) (Real.exp_pos t).le
  rw [← Real.exp_add, show -2 * t + t = -t by ring] at h
  rw [Real.sinh_eq]
  nlinarith

lemma self_le_modelS {κ t : ℝ} (hκ : 0 ≤ κ) (ht : 0 ≤ t) : t ≤ modelS κ t := by
  by_cases hκ0 : κ = 0
  · simp [hκ0]
  · have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hκ0))
    rw [modelS, if_neg hκ0, le_div_iff₀ hs]
    simpa only [mul_comm] using
      Real.self_le_sinh_iff.mpr (mul_nonneg hs.le ht)

lemma modelS_le_mul_exp {κ t : ℝ} (hκ : 0 ≤ κ) :
    modelS κ t ≤ t * Real.exp (Real.sqrt κ * t) := by
  by_cases hκ0 : κ = 0
  · simp [hκ0]
  · have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hκ0))
    rw [modelS, if_neg hκ0, div_le_iff₀ hs]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using sinh_le_mul_exp (Real.sqrt κ * t)

lemma modelVolume_zero_le {n : ℕ} {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r) :
    modelVolume n 0 r ≤ modelVolume n κ r := by
  apply mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_nonneg n))
  apply intervalIntegral.integral_mono_on hr
    (intervalIntegrable_modelS_pow n 0 0 r) (intervalIntegrable_modelS_pow n κ 0 r)
  intro t ht
  simp only [modelS_zero_curvature]
  exact pow_le_pow_left₀ ht.1 (self_le_modelS hκ ht.1) _

lemma modelVolume_le_exp_mul_zero {n : ℕ} {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) :
    modelVolume n κ R ≤ modelVolume n 0 R *
      Real.exp ((n - 1 : ℕ) * (Real.sqrt κ * R)) := by
  let E := Real.exp ((n - 1 : ℕ) * (Real.sqrt κ * R))
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 R) : modelS κ t ^ (n - 1) ≤ t ^ (n - 1) * E := by
    have hs : modelS κ t ≤ t * Real.exp (Real.sqrt κ * R) :=
      (modelS_le_mul_exp hκ).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg κ))) ht.1)
    have hp := pow_le_pow_left₀ (modelS_nonneg hκ ht.1) hs (n - 1)
    simpa only [mul_pow, ← Real.exp_nat_mul, E] using hp
  have hi := intervalIntegral.integral_mono_on hR (intervalIntegrable_modelS_pow n κ 0 R)
    (((continuous_id.pow (n - 1)).mul continuous_const).intervalIntegrable 0 R) hpoint
  change (∫ u in (0 : ℝ)..R, modelS κ u ^ (n - 1)) ≤
    ∫ u in (0 : ℝ)..R, u ^ (n - 1) * E at hi
  rw [intervalIntegral.integral_mul_const] at hi
  have h := mul_le_mul_of_nonneg_left hi
    (mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_nonneg n))
  simpa only [modelVolume, modelS_zero_curvature, mul_assoc, E] using h

lemma modelVolume_div_le {n : ℕ} (hn : 1 ≤ n) {κ r R : ℝ}
    (hκ : 0 ≤ κ) (hr : 0 < r) (hR : 0 ≤ R) :
    modelVolume n κ R / modelVolume n κ r ≤
      (R / r) ^ n * Real.exp ((n - 1 : ℕ) * (Real.sqrt κ * R)) := by
  have hlow := modelVolume_zero_le (n := n) hκ hr.le
  rw [modelVolume_zero_curvature hn] at hlow
  have hden : 0 < euclideanUnitBallVolume n * r ^ n :=
    mul_pos (euclideanUnitBallVolume_pos n) (pow_pos hr _)
  have h := div_le_div₀ (mul_nonneg (modelVolume_nonneg n (by norm_num) hR) (Real.exp_pos _).le)
    (modelVolume_le_exp_mul_zero (n := n) hκ hR) hden hlow
  rw [modelVolume_zero_curvature hn] at h
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [div_pow]
      field_simp [(euclideanUnitBallVolume_pos n).ne', hr.ne']

end PoincareConjecture.RiemannianMetric
