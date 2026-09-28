import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow














open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Poincare.Analysis.RadialIntegration



theorem deriv_le_of_antitone_density_ratio {f : ℝ → ℝ} {t b : ℝ} {k : ℕ}
    (ht : t ∈ Ioo (0 : ℝ) b) (hk : 0 < k) (hf : DifferentiableAt ℝ f t)
    (hanti : AntitoneOn (fun s => f s / s ^ k) (Ioo (0 : ℝ) b)) :
    deriv f t ≤ (k : ℝ) / t * f t := by
  have hd := hf.hasDerivAt.div ((hasDerivAt_id t).pow k) (pow_ne_zero _ ht.1.ne')
  change HasDerivAt (fun s => f s / s ^ k)
    ((deriv f t * t ^ k - f t * ((k : ℝ) * t ^ (k - 1) * 1)) / (t ^ k) ^ 2) t at hd
  have hnonpos := hanti.derivWithin_nonpos (x := t)
  rw [derivWithin_of_isOpen isOpen_Ioo ht, hd.deriv] at hnonpos
  have hn : deriv f t * t ^ k - f t * ((k : ℝ) * t ^ (k - 1)) ≤ 0 := by
    simpa only [mul_one, zero_mul] using (div_le_iff₀ (sq_pos_of_pos
      (pow_pos ht.1 k))).1 hnonpos
  have hp : t ^ k = t ^ (k - 1) * t := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  rw [hp] at hn
  have hmul : deriv f t * t ≤ (k : ℝ) * f t :=
    (mul_le_mul_iff_left₀ (pow_pos ht.1 (k - 1))).1 (by nlinarith [hn])
  calc deriv f t ≤ ((k : ℝ) * f t) / t := (le_div_iff₀ ht.1).2 hmul
    _ = (k : ℝ) / t * f t := by ring



theorem integrableOn_test_mul_bounded_density {f rho : ℝ → ℝ} {c B : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) c))
    (hrho : ContinuousOn rho (Ioo (0 : ℝ) c))
    (hbound : ∀ t ∈ Ioo (0 : ℝ) c, ‖rho t‖ ≤ B) :
    IntegrableOn (fun t => f t * rho t) (Ioo (0 : ℝ) c) := by
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply IntegrableOn.of_bound (by simp : volume (Ioo (0 : ℝ) c) < ⊤)
    ((hf.mono Ioo_subset_Icc_self).mul hrho |>.aestronglyMeasurable measurableSet_Ioo)
    (max P 0 * max B 0)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change ‖f t * rho t‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul ((hP t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _))
    ((hbound t ht).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)




theorem finite_radial_integral_comparison
    {f rho : ℝ → ℝ} {c C d : ℝ} {k : ℕ}
    (hc : 0 < c) (hC : 0 ≤ C) (hk : 0 < k)
    (hf : ContDiff ℝ 1 f) (hfpos : ∀ t ∈ Ioo (0 : ℝ) c, 0 ≤ f t)
    (hrho : ∀ t ∈ Ioo (0 : ℝ) c, DifferentiableAt ℝ rho t)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) c, 0 ≤ rho t ∧ rho t ≤ C * t ^ k)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) c,
      deriv rho t ≤ (k : ℝ) / t * rho t)
    (hzero : Tendsto rho (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hterminal : Tendsto rho (𝓝[<] c) (𝓝 d)) :
    IntegrableOn (fun t => rho t * deriv f t) (Ioo (0 : ℝ) c) ∧
    IntegrableOn (fun t => (k : ℝ) / t * f t * rho t) (Ioo (0 : ℝ) c) ∧
    -(∫ t in Ioo (0 : ℝ) c, rho t * deriv f t) ≤
      (∫ t in Ioo (0 : ℝ) c, (k : ℝ) / t * f t * rho t) - f c * d := by
  have hrcont : ContinuousOn rho (Ioo (0 : ℝ) c) :=
    fun t ht => (hrho t ht).continuousAt.continuousWithinAt
  have hrB : ∀ t ∈ Ioo (0 : ℝ) c, ‖rho t‖ ≤ C * c ^ k := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound t ht).1]
    exact (hbound t ht).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2.le k) hC)
  have hdivB : ∀ t ∈ Ioo (0 : ℝ) c, ‖rho t / t‖ ≤ C * c ^ (k - 1) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hbound t ht).1 ht.1.le)]
    calc rho t / t ≤ C * t ^ k / t :=
          div_le_div_of_nonneg_right (hbound t ht).2 ht.1.le
      _ = C * t ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
        field_simp [ht.1.ne']
      _ ≤ C * c ^ (k - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2.le _) hC
  have hi1 := integrableOn_test_mul_bounded_density
    (hf.continuous_deriv le_rfl).continuousOn hrcont hrB
  have hi2 := integrableOn_test_mul_bounded_density
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => (k : ℝ)) (Icc 0 c)).mul
      hf.continuous.continuousOn)
    (hrcont.div continuousOn_id (fun t ht => ht.1.ne')) hdivB
  have hi1' : IntegrableOn (fun t => rho t * deriv f t) (Ioo (0 : ℝ) c) := by
    simpa only [mul_comm] using hi1
  have hi2' : IntegrableOn (fun t => (k : ℝ) / t * f t * rho t)
      (Ioo (0 : ℝ) c) := by
    convert hi2 using 1
    ext t
    change (k : ℝ) / t * f t * rho t = ((k : ℝ) * f t) * (rho t / t)
    ring
  refine ⟨hi1', hi2', ?_⟩
  let F := Function.update (Function.update (fun t => f t * rho t) 0 0) c (f c * d)
  have hFderiv : ∀ t ∈ Ioo (0 : ℝ) c,
      HasDerivAt F (deriv f t * rho t + f t * deriv rho t) t := by
    intro t ht
    apply ((hf.differentiable (by norm_num) t).hasDerivAt.mul
      (hrho t ht).hasDerivAt).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    simp only [F, Function.update_of_ne hs.2.ne, Function.update_of_ne hs.1.ne', Pi.mul_apply]
  have hFcont : ContinuousOn F (Icc (0 : ℝ) c) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_sdiff_right, Ico_sdiff_left]
    refine ⟨⟨fun t ht => ((hf.differentiable (by norm_num) t).hasDerivAt.mul
      (hrho t ht).hasDerivAt).continuousAt.continuousWithinAt, ?_⟩, ?_⟩
    · intro _
      have hz := ((hf.continuous.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).mul hzero
      simp only [mul_zero] at hz
      exact hz.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · intro _
      have hz := ((hf.continuous.tendsto c).mono_left nhdsWithin_le_nhds).mul hterminal
      refine (hz.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsLT hc] with t ht
      simp [ht.1.ne']
  have hsum : IntegrableOn (fun t => deriv f t * rho t + (k : ℝ) / t * f t * rho t)
      (Icc (0 : ℝ) c) := (integrableOn_Icc_iff_integrableOn_Ioo (by finiteness)
        (by finiteness)).2 (hi1.add hi2')
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hc.le hFcont
    (fun t ht => (hFderiv t ht).hasDerivWithinAt) hsum (fun t ht => by
      have hh := mul_le_mul_of_nonneg_left (hderiv t ht) (hfpos t ht)
      nlinarith)
  have hii1 := (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le).2 hi1
  have hii2 := (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le).2 hi2'
  rw [intervalIntegral.integral_add hii1 hii2,
    intervalIntegral.integral_of_le hc.le, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hc.le, integral_Ioc_eq_integral_Ioo] at h
  simp [F, hc.ne] at h
  have heq : (∫ t in Ioo (0 : ℝ) c, deriv f t * rho t) =
      ∫ t in Ioo (0 : ℝ) c, rho t * deriv f t := by congr 1; ext t; ring
  rw [heq] at h
  linarith




theorem radial_integral_comparison_of_antitone
    {f H : ℝ → ℝ} {c : ℝ} {k : ℕ} (hc : 0 < c) (hk : 0 < k)
    (hf : ContDiff ℝ 1 f) (hfpos : ∀ t ∈ Icc (0 : ℝ) c, 0 ≤ f t)
    (hH : ContinuousOn H (Icc (0 : ℝ) c))
    (hdiff : ∀ t ∈ Ioo (0 : ℝ) c, DifferentiableAt ℝ H t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) c, 0 ≤ H t)
    (hanti : AntitoneOn H (Ioo (0 : ℝ) c)) :
    IntegrableOn (fun t => (t ^ k * H t) * deriv f t) (Ioo (0 : ℝ) c) ∧
    IntegrableOn (fun t => (k : ℝ) / t * f t * (t ^ k * H t)) (Ioo (0 : ℝ) c) ∧
    -(∫ t in Ioo (0 : ℝ) c, (t ^ k * H t) * deriv f t) ≤
      ∫ t in Ioo (0 : ℝ) c, (k : ℝ) / t * f t * (t ^ k * H t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  let rho := fun t : ℝ => t ^ k * H t
  have hrho : ContinuousOn rho (Icc (0 : ℝ) c) :=
    (continuousOn_id.pow k).mul hH
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) c) : DifferentiableAt ℝ rho t :=
    (differentiableAt_id.pow k).mul (hdiff t ht)
  have hbound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) c) :
      0 ≤ rho t ∧ rho t ≤ max C 0 * t ^ k := by
    have ht' := Ioo_subset_Icc_self ht
    have hHle : H t ≤ max C 0 :=
      (le_abs_self _).trans ((hC t ht').trans (le_max_left _ _))
    exact ⟨mul_nonneg (pow_nonneg ht.1.le k) (hpos t ht'), by
      simpa only [rho, mul_comm] using
        mul_le_mul_of_nonneg_right hHle (pow_nonneg ht.1.le k)⟩
  have hratio : AntitoneOn (fun t => rho t / t ^ k) (Ioo (0 : ℝ) c) := by
    intro x hx y hy hxy
    simpa only [rho, mul_div_cancel_left₀ _ (pow_ne_zero _ hx.1.ne'),
      mul_div_cancel_left₀ _ (pow_ne_zero _ hy.1.ne')] using hanti hx hy hxy
  have hz : Tendsto rho (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hrho 0 ⟨le_rfl, hc.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hc)
    change Tendsto rho (𝓝[>] (0 : ℝ)) (𝓝 (rho 0)) at h
    simpa only [rho, zero_pow hk.ne', zero_mul] using h
  have hend : Tendsto rho (𝓝[<] c) (𝓝 (rho c)) :=
    (hrho c ⟨hc.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hc)
  obtain ⟨hi1, hi2, hineq⟩ := finite_radial_integral_comparison hc (le_max_right _ _) hk
    hf (fun t ht => hfpos t (Ioo_subset_Icc_self ht)) hd hbound
    (fun t ht => deriv_le_of_antitone_density_ratio ht hk (hd t ht) hratio) hz hend
  refine ⟨hi1, hi2, hineq.trans ?_⟩
  exact sub_le_self _ (mul_nonneg (hfpos c ⟨hc.le, le_rfl⟩)
    (mul_nonneg (pow_nonneg hc.le k) (hpos c ⟨hc.le, le_rfl⟩)))

end Poincare.Analysis.RadialIntegration
