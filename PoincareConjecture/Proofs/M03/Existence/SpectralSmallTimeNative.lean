import PoincareConjecture.Proofs.M03.Existence.SpectralTraceNative
import PoincareConjecture.Proofs.M03.Existence.SpectralL2ResponseNative










set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace PoincareConjecture.SpectralHeatNative


theorem integral_sq_le_time_mul_integral_sq {T : ℝ} (hT : 0 ≤ T)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 T)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T, f t) ^ 2 ≤ T * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    simp
  let a : ℝ := ∫ t in (0 : ℝ)..T, f t
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T, (T * f t - a) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)
  have heq : (∫ t in (0 : ℝ)..T, (T * f t - a) ^ 2) =
      T ^ 2 * (∫ t in (0 : ℝ)..T, f t ^ 2) - 2 * T * a * a + T * a ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..T, T ^ 2 * f t ^ 2 - (2 * T * a) * f t + a ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hf2.const_mul (T ^ 2)).sub (hf.const_mul (2 * T * a)))
          intervalIntegrable_const,
          intervalIntegral.integral_sub (hf2.const_mul (T ^ 2))
            (hf.const_mul (2 * T * a)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        rfl
  have hprod : 0 ≤ T * (T * (∫ t in (0 : ℝ)..T, f t ^ 2) - a ^ 2) := by
    rw [heq] at hnonneg
    nlinarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod hpos)

theorem norm_integral_sq_le_time_energy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} (hT : 0 ≤ T) {f : ℝ → E}
    (hf : MemLp f 2 (timeMeasure T)) :
    ‖∫ t in (0 : ℝ)..T, f t‖ ^ 2 ≤ T * ∫ t, ‖f t‖ ^ 2 ∂timeMeasure T := by
  obtain ⟨hi, hi2⟩ := intervalIntegrable_and_sq_of_memLp_two hT hf.norm
  have hnorm : ‖∫ t in (0 : ℝ)..T, f t‖ ≤ ∫ t in (0 : ℝ)..T, ‖f t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hT
  have hsq := integral_sq_le_time_mul_integral_sq hT hi hi2
  simpa only [intervalIntegral.integral_of_le hT] using
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsq

variable {iota : Type*} [Countable iota]


theorem norm_responseState_sq_le_time_energy {T t : ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (lambda : iota → NNReal)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖responseState lambda F t‖ ^ 2 ≤ t * ∫ s, ‖F s‖ ^ 2 ∂timeMeasure T := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hD := memLp_derivativeState_of_memLp hT hF lambda
  have hDprefix : MemLp (derivativeState lambda F) 2 (timeMeasure t) :=
    hD.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl)
  have hbound := norm_integral_sq_le_time_energy ht.1 hDprefix
  have hmono : (∫ s, ‖derivativeState lambda F s‖ ^ 2 ∂timeMeasure t) ≤
      ∫ s, ‖derivativeState lambda F s‖ ^ 2 ∂timeMeasure T := by
    apply integral_mono_measure
      (Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    exact (memLp_two_iff_integrable_sq_norm hD.1).mp hD
  have henergy := integral_response_energy_le_of_memLp hT hF lambda
  have hgen : 0 ≤ ∫ s, ‖generatorState lambda F s‖ ^ 2 ∂timeMeasure T :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hDle : (∫ s, ‖derivativeState lambda F s‖ ^ 2 ∂timeMeasure T) ≤
      ∫ s, ‖F s‖ ^ 2 ∂timeMeasure T := by linarith
  exact hbound.trans (mul_le_mul_of_nonneg_left (hmono.trans hDle) ht.1)

theorem memLp_responseState_of_memLp {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) : MemLp (responseState lambda F) 2 (timeMeasure T) := by
  have hc := continuousOn_responseState_of_memLp hT hF lambda
  apply (memLp_two_iff_integrable_sq_norm
    ((hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
  exact (hc.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self


theorem integral_response_sq_le_time_sq {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    (∫ t, ‖responseState lambda F t‖ ^ 2 ∂timeMeasure T) ≤
      T ^ 2 * ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  let energy : ℝ := ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T
  have he : 0 ≤ energy := integral_nonneg (fun _ => sq_nonneg _)
  have hu := memLp_responseState_of_memLp hT hF lambda
  calc
    _ ≤ ∫ _t, T * energy ∂timeMeasure T := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hu.1).mp hu)
        (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (norm_responseState_sq_le_time_energy hF lambda
        (Ioc_subset_Icc_self ht)).trans (mul_le_mul_of_nonneg_right ht.2 he)
    _ = _ := by
      simp [energy, timeMeasure, integral_const, Measure.real, Real.volume_Ioc, hT,
        ENNReal.toReal_ofReal, pow_two, mul_assoc]

theorem memLp_traceState {T : ℝ} (hT : 0 ≤ T) {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (lambda : iota → NNReal) :
    MemLp (SpectralTraceNative.traceState lambda F) 2 (timeMeasure T) := by
  have hc := SpectralTraceNative.continuousOn_traceState hT hF lambda
  apply (memLp_two_iff_integrable_sq_norm
    ((hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
  exact (hc.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self


theorem integral_trace_sq_le_time {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    (∫ t, ‖SpectralTraceNative.traceState lambda F t‖ ^ 2 ∂timeMeasure T) ≤
      T * ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  have hu := memLp_traceState hT hF lambda
  calc
    _ ≤ ∫ _t, (∫ s, ‖F s‖ ^ 2 ∂timeMeasure T) ∂timeMeasure T := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hu.1).mp hu)
        (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact SpectralTraceNative.norm_traceState_sq_le hF lambda (Ioc_subset_Icc_self ht)
    _ = _ := by
      simp [timeMeasure, integral_const, Measure.real, Real.volume_Ioc, hT,
        ENNReal.toReal_ofReal]

end PoincareConjecture.SpectralHeatNative
