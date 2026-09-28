import PoincareConjecture.Statements.M64Comparison
import Mathlib.Analysis.Real.Pi.Bounds











set_option autoImplicit false

namespace PoincareConjecture




theorem m64Intrinsic_exists_comparison_base_scale
    (K : ℝ) {delta r : ℝ} (hdelta : 0 < delta)
    (hdelta100 : delta < 1 / 100) (hr : 0 < r) :
    ∃ q alpha : ℝ, 0 < q ∧ 2 * q ≤ r ∧ q ≤ r ∧
      Real.sqrt (max K 1) * q ≤ 1 / 2 ∧ 0 ≤ alpha ∧
      alpha = 100 * delta / q ∧ 4 * (q / 10) * alpha < 1 ∧
      q / 10 ≤ 3 * q / (1600 * delta) := by
  let kappa : ℝ := Real.sqrt (max K 1)
  have hkappa : 0 < kappa :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1))
  let q : ℝ := min (r / 2) (1 / (2 * kappa))
  have hq : 0 < q := lt_min (by positivity) (by positivity)
  have hqr : q ≤ r / 2 := min_le_left _ _
  have hqkappa : q * (2 * kappa) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * kappa)).mp (min_le_right _ _)
  let alpha : ℝ := 100 * delta / q
  have halpha : 0 ≤ alpha := by dsimp [alpha]; positivity
  have halphaq : alpha * q = 100 * delta :=
    (eq_div_iff hq.ne').mp rfl
  refine ⟨q, alpha, hq, by linarith, by linarith, ?_, halpha, rfl, ?_, ?_⟩
  · change kappa * q ≤ 1 / 2
    nlinarith only [hqkappa]
  · nlinarith only [halphaq, hdelta100]
  · apply (le_div_iff₀ (by positivity : 0 < 1600 * delta)).mpr
    nlinarith only [mul_lt_mul_of_pos_right hdelta100 hq, hq]




theorem m64Intrinsic_exists_comparison_area_cutoff
    (K : ℝ) {delta q R0 : ℝ} (hdelta100 : delta < 1 / 100)
    (hq : 0 < q) (hR0 : 0 < R0) :
    ∃ h mu : ℝ, 0 < h ∧ h ≤ q / 100 ∧ h ≤ R0 ∧ 0 < mu ∧
      mu ≤ (1 - delta) ^ 2 * h * (q / 10) ∧
      max K 0 * mu + delta ≤ Real.pi / 2 := by
  let kappa : ℝ := Real.sqrt (max K 1)
  have hmax : 0 < max K 1 := zero_lt_one.trans_le (le_max_right K 1)
  have hkappa : 0 < kappa := Real.sqrt_pos.mpr hmax
  have hkappa_sq : kappa ^ 2 = max K 1 := Real.sq_sqrt hmax.le
  let h : ℝ := min (q / 100) R0
  have hh : 0 < h := lt_min (by positivity) hR0
  have hdelta1 : 0 < 1 - delta := by linarith only [hdelta100]
  let mu : ℝ := min ((1 - delta) ^ 2 * h * (q / 10)) (1 / (100 * kappa ^ 2))
  have hmu : 0 < mu := lt_min (by positivity) (by positivity)
  have hmu_model : mu * (100 * kappa ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 100 * kappa ^ 2)).mp (min_le_right _ _)
  have hcurvature : max K 0 ≤ kappa ^ 2 := by
    rw [hkappa_sq]
    exact max_le (le_max_left K 1) hmax.le
  have hbudget : max K 0 * mu ≤ 1 / 100 := by
    have hcompare := mul_le_mul_of_nonneg_right hcurvature hmu.le
    nlinarith only [hmu_model, hcompare]
  exact ⟨h, mu, hh, min_le_left _ _, min_le_right _ _, hmu,
    min_le_left _ _, by linarith only [hbudget, hdelta100, Real.pi_gt_three]⟩

end PoincareConjecture
