import PoincareConjecture.Proofs.M65.Mathlib.Plateau.DiskNormalization

set_option autoImplicit false

namespace Complex

theorem plateauCayley_eq_re {z : ℂ} (hz : ‖z‖ = 1) :
    I * (1 + z) / (1 - z) = ((I * (1 + z) / (1 - z)).re : ℂ) := by
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := normSq_eq_norm_sq z
    rw [hz, one_pow, normSq_apply] at h
    nlinarith only [h]
  apply Complex.ext
  · rfl
  · rw [ofReal_im, div_im]
    simp only [mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im,
      sub_re, sub_im, zero_mul, one_mul, zero_add, zero_sub, mul_neg, neg_mul, neg_neg]
    rw [← sub_div]
    have hzero : (1 + z.re) * (1 - z.re) - z.im * z.im = 0 := by nlinarith
    rw [hzero, zero_div]

theorem plateauCayley_injective {z w : ℂ} (hz : z ≠ 1) (hw : w ≠ 1)
    (heq : I * (1 + z) / (1 - z) = I * (1 + w) / (1 - w)) : z = w := by
  have h := (div_eq_div_iff (sub_ne_zero.mpr hz.symm) (sub_ne_zero.mpr hw.symm)).mp heq
  have hcross : (1 + z) * (1 - w) = (1 + w) * (1 - z) := by
    apply mul_left_cancel₀ I_ne_zero
    simpa only [mul_assoc] using h
  linear_combination (1 / 2 : ℂ) * hcross

theorem plateauDiskMap_pin (b : ℝ) {c : ℝ} (hc : 0 < c)
    {z w value : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1)
    (hCayley : I * (1 + z) / (1 - z) = w)
    (hvalue : w - b - I * c = value * (w - b + I * c)) :
    plateauDiskMap b c z = value := by
  have hH := (div_eq_iff (sub_ne_zero.mpr hz1.symm)).mp hCayley
  have hsum : z + 1 = -I * w * (1 - z) := by
    calc
      z + 1 = -I * (I * (1 + z)) := by simp [← mul_assoc, add_comm]
      _ = -I * (w * (1 - z)) := by rw [hH]
      _ = _ := by ring
  apply (div_eq_iff (plateauDiskDenominator_ne_zero b hc hz)).mpr
  dsimp only [plateauDiskNumerator, plateauDiskDenominator]
  rw [hsum]
  calc
    _ = -I * (w - b - I * c) * (1 - z) := by
      ring_nf
      simp [I_sq]
      ring
    _ = -I * (value * (w - b + I * c)) * (1 - z) := by rw [hvalue]
    _ = _ := by
      ring_nf
      simp [I_sq]
      ring

theorem exists_plateauDiskMap_pins {q r : ℂ} (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hq1 : q ≠ 1) (hr1 : r ≠ 1) (hqr : q ≠ r) :
    ∃ b c : ℝ, 0 < c ∧ plateauDiskMap b c 1 = 1 ∧
      plateauDiskMap b c q = -1 ∧
      (plateauDiskMap b c r = I ∨ plateauDiskMap b c r = -I) := by
  let x := (I * (1 + q) / (1 - q)).re
  let y := (I * (1 + r) / (1 - r)).re
  have hqx : I * (1 + q) / (1 - q) = (x : ℂ) := plateauCayley_eq_re hq
  have hry : I * (1 + r) / (1 - r) = (y : ℂ) := plateauCayley_eq_re hr
  have hxy : x ≠ y := by
    intro heq
    apply hqr
    exact plateauCayley_injective hq1 hr1 (hqx.trans ((congrArg ofReal heq).trans hry.symm))
  have hone (b c : ℝ) : plateauDiskMap b c 1 = 1 := by
    norm_num [plateauDiskMap, plateauDiskNumerator, plateauDiskDenominator]
  have hqpin {c : ℝ} (hc : 0 < c) : plateauDiskMap x c q = -1 :=
    plateauDiskMap_pin x hc hq.le hq1 hqx (by ring)
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · refine ⟨x, y - x, sub_pos.mpr hlt, hone _ _, hqpin (sub_pos.mpr hlt), Or.inr ?_⟩
    apply plateauDiskMap_pin x (sub_pos.mpr hlt) hr.le hr1 hry
    push_cast
    ring_nf
    simp [I_sq]
    ring
  · refine ⟨x, x - y, sub_pos.mpr hgt, hone _ _, hqpin (sub_pos.mpr hgt), Or.inl ?_⟩
    apply plateauDiskMap_pin x (sub_pos.mpr hgt) hr.le hr1 hry
    push_cast
    ring_nf
    simp [I_sq]
    ring

end Complex
