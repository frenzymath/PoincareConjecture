import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverTotalEnergy
import Mathlib.MeasureTheory.Integral.Average














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M64Uniformization







theorem scalar_exists_energy_radius {F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : IntegrableOn F (Ioo a b)) (hnon : ∀ r ∈ Ioo a b, 0 ≤ F r) :
    ∃ r ∈ Ioo a b,
      (r - a) * F r ≤ ∫ s in Ioo a b, F s ∧
      (b - r) * F r ≤ ∫ s in Ioo a b, F s := by
  have hvol : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  obtain ⟨r, hr, havg⟩ := exists_le_setAverage hvol (by simp) hF
  have hmean : F r ≤ (∫ s in Ioo a b, F s) / (b - a) := by
    simpa only [setAverage_eq, Real.volume_real_Ioo_of_le hab.le,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using havg
  have hbound := (le_div_iff₀ (sub_pos.mpr hab)).mp hmean
  refine ⟨r, hr, ?_, ?_⟩
  · calc
      (r - a) * F r ≤ (b - a) * F r :=
        mul_le_mul_of_nonneg_right (sub_le_sub_right hr.2.le a) (hnon r hr)
      _ ≤ _ := by simpa only [mul_comm] using hbound
  · calc
      (b - r) * F r ≤ (b - a) * F r :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hr.1.le b) (hnon r hr)
      _ ≤ _ := by simpa only [mul_comm] using hbound







theorem scalar_exists_inner_small_energy_radius {F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : IntegrableOn F (Ioo a b)) (hnon : ∀ r ∈ Ioo a b, 0 ≤ F r)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∃ r ∈ Ioo a b, r - a < delta ∧ (r - a) * F r < epsilon := by
  let G : ℝ → ℝ := (Ioo a b).indicator F
  have hG : Integrable G := (integrable_indicator_iff measurableSet_Ioo).mpr hF
  have hc := hG.continuous_primitive a
  obtain ⟨eta, heta, hsmall⟩ := Metric.continuousAt_iff.mp hc.continuousAt epsilon hepsilon
  let ell := min (b - a) (min delta eta)
  have hell : 0 < ell := lt_min (sub_pos.mpr hab) (lt_min hdelta heta)
  have hellb : ell ≤ b - a := min_le_left _ _
  have helld : ell ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
  have helle : ell ≤ eta := (min_le_right _ _).trans (min_le_right _ _)
  let c := a + ell / 2
  have hac : a < c := by dsimp only [c]; linarith
  have hcb : c < b := by dsimp only [c]; linarith
  have hcnear : dist c a < eta := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hac)]
    dsimp only [c]
    linarith
  have hsmallc : |∫ s in a..c, G s| < epsilon := by
    simpa only [intervalIntegral.integral_same, dist_zero_right, Real.norm_eq_abs]
      using hsmall hcnear
  have hsub : Ioo a c ⊆ Ioo a b := fun r hr => ⟨hr.1, hr.2.trans hcb⟩
  have hident : (∫ s in Ioo a c, F s) = ∫ s in a..c, G s := by
    rw [intervalIntegral.integral_of_le hac.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    exact (indicator_of_mem (hsub hr) F).symm
  obtain ⟨r, hr, hbound, -⟩ := scalar_exists_energy_radius hac (hF.mono_set hsub)
    (fun r hr => hnon r (hsub hr))
  refine ⟨r, hsub hr, ?_, ?_⟩
  · dsimp only [c] at hr
    linarith [hr.2]
  · exact hbound.trans_lt (hident ▸ (le_abs_self _).trans_lt hsmallc)






theorem scalar_exists_outer_small_energy_radius {F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : IntegrableOn F (Ioo a b)) (hnon : ∀ r ∈ Ioo a b, 0 ≤ F r)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∃ r ∈ Ioo a b, b - r < delta ∧ (b - r) * F r < epsilon := by
  let G : ℝ → ℝ := (Ioo a b).indicator F
  have hG : Integrable G := (integrable_indicator_iff measurableSet_Ioo).mpr hF
  have hc := hG.continuous_primitive b
  obtain ⟨eta, heta, hsmall⟩ := Metric.continuousAt_iff.mp hc.continuousAt epsilon hepsilon
  let ell := min (b - a) (min delta eta)
  have hell : 0 < ell := lt_min (sub_pos.mpr hab) (lt_min hdelta heta)
  have hellb : ell ≤ b - a := min_le_left _ _
  have helld : ell ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
  have helle : ell ≤ eta := (min_le_right _ _).trans (min_le_right _ _)
  let c := b - ell / 2
  have hac : a < c := by dsimp only [c]; linarith
  have hcb : c < b := by dsimp only [c]; linarith
  have hcnear : dist c b < eta := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hcb)]
    dsimp only [c]
    linarith
  have hsmallc : |∫ s in c..b, G s| < epsilon := by
    rw [intervalIntegral.integral_symm, abs_neg]
    simpa only [intervalIntegral.integral_same, dist_zero_right, Real.norm_eq_abs]
      using hsmall hcnear
  have hsub : Ioo c b ⊆ Ioo a b := fun r hr => ⟨hac.trans hr.1, hr.2⟩
  have hident : (∫ s in Ioo c b, F s) = ∫ s in c..b, G s := by
    rw [intervalIntegral.integral_of_le hcb.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    exact (indicator_of_mem (hsub hr) F).symm
  obtain ⟨r, hr, -, hbound⟩ := scalar_exists_energy_radius hcb (hF.mono_set hsub)
    (fun r hr => hnon r (hsub hr))
  refine ⟨r, hsub hr, ?_, ?_⟩
  · dsimp only [c] at hr
    linarith [hr.1]
  · exact hbound.trans_lt (hident ▸ (le_abs_self _).trans_lt hsmallc)

end PoincareConjecture.M64Uniformization
