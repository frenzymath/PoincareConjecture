import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in

theorem integral_norm_le_sqrt_energy {d : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hd : MemLp d 2 (volume.restrict (Icc a b))) :
    (∫ s in a..b, ‖d s‖) ≤
      Real.sqrt (∫ s in a..b, ‖d s‖ ^ 2) * Real.sqrt (b - a) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ (fun s => norm_nonneg (d s)))
    (ae_of_all _ (fun _ => (zero_le_one : (0 : ℝ) ≤ 1)))
    (by simpa using hd.norm) (memLp_const (1 : ℝ))
  simpa only [mul_one, Real.rpow_two, one_pow, ← Real.sqrt_eq_rpow,
    setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le hab,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] using h

theorem norm_sub_sq_le_interval_energy {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    ‖f b - f a‖ ^ 2 ≤ (b - a) * ∫ s in a..b, ‖deriv f s‖ ^ 2 := by
  have hi : IntervalIntegrable (fun s => ‖deriv f s‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (hd.norm.integrable (by norm_num))
  have hdisp := norm_sub_le_integral_of_norm_deriv_le_of_le hab hf hdf
    (ae_of_all _ (fun _ _ => le_rfl)) hi
  have hbound := hdisp.trans (integral_norm_le_sqrt_energy hab hd)
  have henergy : 0 ≤ ∫ s in a..b, ‖deriv f s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hsq := sq_le_sq₀ (norm_nonneg (f b - f a)) (by positivity) |>.mpr hbound
  rw [mul_pow, Real.sq_sqrt henergy, Real.sq_sqrt (sub_nonneg.mpr hab), mul_comm] at hsq
  exact hsq

theorem norm_sub_sq_le_total_interval_energy {f : ℝ → E} {a b s : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) (hs : s ∈ Icc a b) :
    ‖f b - f s‖ ^ 2 ≤ (b - s) * ∫ t in a..b, ‖deriv f t‖ ^ 2 := by
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc hs.1 le_rfl
  have hder := hd.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h := norm_sub_sq_le_interval_energy hs.2 (hf.mono hsub)
    (hdf.mono (Ioo_subset_Ioo hs.1 le_rfl)) hder
  have he : IntervalIntegrable (fun t => ‖deriv f t‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hs.1.trans hs.2)).mpr
      ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd)
  exact h.trans (mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
      (ae_of_all _ (fun _ => sq_nonneg _)) he) (sub_nonneg.mpr hs.2))

theorem tendsto_endpoint_displacement_quotient {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    Tendsto (fun t => ‖f b - f t‖ ^ 2 / (b - t)) (𝓝[Icc a b] b) (𝓝 0) := by
  have he : IntegrableOn (fun s => ‖deriv f s‖ ^ 2) (Icc a b) :=
    (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have he' : IntegrableOn (fun s => ‖deriv f s‖ ^ 2) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using he
  have hc := intervalIntegral.continuousOn_primitive_interval_left he'
  rw [uIcc_of_le hab] at hc
  have hlim : Tendsto (fun t => ∫ s in t..b, ‖deriv f s‖ ^ 2)
      (𝓝[Icc a b] b) (𝓝 0) := by
    simpa only [ContinuousWithinAt, intervalIntegral.integral_same] using hc b ⟨hab, le_rfl⟩
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr ht.2)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rcases ht.2.eq_or_lt with htb | htb
    · subst t
      simp
    · have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
      have hder : MemLp (deriv f) 2 (volume.restrict (Icc t b)) :=
        hd.mono_measure (Measure.restrict_mono hsub le_rfl)
      have h := norm_sub_sq_le_interval_energy htb.le (hf.mono hsub)
        (hdf.mono (Ioo_subset_Ioo ht.1 le_rfl)) hder
      exact (div_le_iff₀ (sub_pos.mpr htb)).mpr (by simpa only [mul_comm] using h)

end PoincareConjecture.M14
