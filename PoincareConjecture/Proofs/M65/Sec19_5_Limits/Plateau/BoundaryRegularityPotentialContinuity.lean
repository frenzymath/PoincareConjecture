import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeightedPotential
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyContinuity

set_option autoImplicit false

open Set Metric MeasureTheory Complex Filter
open scoped Topology

namespace PoincareConjecture.M65Boundary

open M65Branch

private theorem inverse_le_weight {a r δ : ℝ} (ha : 1 < a)
    (hr : 0 ≤ r) (hδ : 0 < δ) (hrδ : r ≤ δ) :
    r⁻¹ ≤ δ ^ (a - 1) * r ^ (-a) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [inv_zero]
    positivity
  calc
    r⁻¹ = r ^ (a - 1) * r ^ (-a) := by
      rw [← Real.rpow_add hr, show a - 1 + -a = -1 by ring, Real.rpow_neg_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hr.le hrδ (by linarith)) (Real.rpow_nonneg hr.le _)

theorem integrable_cauchy_of_weight {a : ℝ} (ha : 1 < a) {h : ℂ → ℂ}
    (hh : Integrable h) (x : ℂ)
    (hw : Integrable (fun w => ‖h w‖ * ‖x - w‖ ^ (-a))) :
    Integrable (fun w => (x - w)⁻¹ * h w) := by
  apply (hh.norm.add hw).mono'
    ((measurable_const.sub measurable_id).inv.aestronglyMeasurable.mul hh.1)
  filter_upwards [] with w
  have hi : ‖x - w‖⁻¹ ≤ 1 + ‖x - w‖ ^ (-a) := by
    by_cases hr : ‖x - w‖ ≤ 1
    · have h := inverse_le_weight ha (norm_nonneg _) zero_lt_one hr
      simp only [Real.one_rpow, one_mul] at h
      linarith
    · have h1 : 1 ≤ ‖x - w‖ := le_of_lt (lt_of_not_ge hr)
      have h2 := (inv_le_one₀ (zero_lt_one.trans_le h1)).mpr h1
      exact h2.trans (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
  change ‖(x - w)⁻¹ * h w‖ ≤ ‖h w‖ + ‖h w‖ * ‖x - w‖ ^ (-a)
  simp only [norm_mul, norm_inv]
  have hi' := mul_le_mul_of_nonneg_right hi (norm_nonneg (h w))
  nlinarith only [hi']

private theorem regularized_integrable_L1 {δ : ℝ} (hδ : 0 < δ)
    {h : ℂ → ℂ} (hh : Integrable h) (x : ℂ) :
    Integrable (fun w => regularizedCauchyKernel δ (x - w) * h w) := by
  apply (hh.norm.const_mul δ⁻¹).mono'
    (((continuous_regularizedCauchyKernel hδ).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hh.1)
  filter_upwards [] with w
  change ‖regularizedCauchyKernel δ (x - w) * h w‖ ≤ δ⁻¹ * ‖h w‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_regularizedCauchyKernel_le hδ _)
    (norm_nonneg _)

private theorem regularized_continuous_L1 {δ : ℝ} (hδ : 0 < δ)
    {h : ℂ → ℂ} (hh : Integrable h) :
    Continuous (regularizedCauchyOperator δ h) := by
  have hk := continuous_regularizedCauchyKernel hδ
  have hi : Continuous (fun x : ℂ => ∫ w, regularizedCauchyKernel δ (x - w) * h w) := by
    apply continuous_of_dominated (bound := fun w => δ⁻¹ * ‖h w‖)
    · intro x
      exact (hk.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hh.1
    · intro x
      filter_upwards [] with w
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_regularizedCauchyKernel_le hδ _)
        (norm_nonneg _)
    · exact hh.norm.const_mul _
    · exact ae_of_all _ fun w =>
        (hk.comp (continuous_id.sub continuous_const)).mul continuous_const
  simpa +instances only [regularizedCauchyOperator, smul_eq_mul] using!
    hi.const_mul (Real.pi : ℂ)⁻¹

theorem cauchy_regularization_weighted_error {a δ B : ℝ}
    (ha : 1 < a) (hδ : 0 < δ) {h : ℂ → ℂ} (hh : Integrable h) (x : ℂ)
    (hw : Integrable (fun w => ‖h w‖ * ‖x - w‖ ^ (-a)))
    (hb : (∫ w, ‖h w‖ * ‖x - w‖ ^ (-a)) ≤ B) :
    ‖cauchyOperator h x - regularizedCauchyOperator δ h x‖ ≤
      (2 / Real.pi) * δ ^ (a - 1) * B := by
  have h0 := integrable_cauchy_of_weight ha hh x hw
  have h1 := regularized_integrable_L1 hδ hh x
  let G := fun w => ((x - w)⁻¹ - regularizedCauchyKernel δ (x - w)) * h w
  have hi : Integrable G := by
    simpa +instances only [G, sub_mul, Pi.sub_apply] using! h0.sub h1
  have hpoint (w : ℂ) : ‖G w‖ ≤
      (2 * δ ^ (a - 1)) * (‖h w‖ * ‖x - w‖ ^ (-a)) := by
    have hk := norm_sub_regularizedCauchyKernel_le hδ (x - w)
    by_cases hr : ‖x - w‖ < δ
    · rw [indicator_of_mem (mem_ball_zero_iff.mpr hr)] at hk
      have hp := inverse_le_weight ha (norm_nonneg _) hδ hr.le
      calc
        ‖G w‖ = ‖(x - w)⁻¹ - regularizedCauchyKernel δ (x - w)‖ * ‖h w‖ := norm_mul _ _
        _ ≤ (2 * ‖x - w‖⁻¹) * ‖h w‖ := mul_le_mul_of_nonneg_right hk (norm_nonneg _)
        _ ≤ (2 * (δ ^ (a - 1) * ‖x - w‖ ^ (-a))) * ‖h w‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (norm_nonneg _)
        _ = _ := by ring
    · have heq := regularizedCauchyKernel_eq_inv hδ (le_of_not_gt hr)
      simp only [G, heq, sub_self, zero_mul, norm_zero]
      positivity
  have hbound : ‖∫ w, G w‖ ≤ (2 * δ ^ (a - 1)) * B := by
    calc
      _ ≤ ∫ w, ‖G w‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w, (2 * δ ^ (a - 1)) * (‖h w‖ * ‖x - w‖ ^ (-a)) :=
        integral_mono_ae hi.norm (hw.const_mul _) (ae_of_all _ hpoint)
      _ = (2 * δ ^ (a - 1)) * ∫ w, ‖h w‖ * ‖x - w‖ ^ (-a) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  have heq : cauchyOperator h x - regularizedCauchyOperator δ h x =
      (Real.pi : ℂ)⁻¹ * ∫ w, G w := by
    rw [cauchyOperator, regularizedCauchyOperator]
    simp only [smul_eq_mul, G, sub_mul, integral_sub h0 h1]
    ring
  rw [heq, norm_mul, norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * ((2 * δ ^ (a - 1)) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

theorem continuousOn_cauchy_of_uniform_weight {a B : ℝ} (ha : 1 < a)
    {h : ℂ → ℂ} (hh : Integrable h) {U : Set ℂ}
    (hw : ∀ x ∈ U, Integrable (fun w => ‖h w‖ * ‖x - w‖ ^ (-a)))
    (hb : ∀ x ∈ U, (∫ w, ‖h w‖ * ‖x - w‖ ^ (-a)) ≤ B) :
    ContinuousOn (cauchyOperator h) U := by
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hp := hδlim.rpow_const_nhds_zero (by linarith : 0 < a - 1)
  have hlim : Tendsto (fun n => (2 / Real.pi) * δ n ^ (a - 1) * B) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hp.const_mul (2 / Real.pi)).mul_const B
  have hu : TendstoUniformlyOn (fun n => regularizedCauchyOperator (δ n) h)
      (cauchyOperator h) atTop U := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn x hx
    rw [dist_eq_norm]
    exact (cauchy_regularization_weighted_error ha (hδ n) hh x (hw x hx) (hb x hx)).trans_lt hn
  apply hu.continuousOn
  exact (Eventually.of_forall fun n =>
    (regularized_continuous_L1 (hδ n) hh).continuousOn).frequently

end PoincareConjecture.M65Boundary
