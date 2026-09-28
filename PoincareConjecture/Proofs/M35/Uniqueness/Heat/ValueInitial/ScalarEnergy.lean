import PoincareConjecture.Proofs.M03.Existence.SpectralParabolicNative









set_option autoImplicit false

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

theorem scalar_heat_form_energy {T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (c : ℝ) :
    (∫ t in (0 : ℝ)..T, (Real.sqrt (1 + a) * Real.exp (-t * a) * c) ^ 2) ≤
      (T + 1 / 2) * c ^ 2 := by
  let w : ℝ → ℝ := fun t => Real.exp (-2 * t * a)
  have hw : Continuous w := by fun_prop
  have hv : (∫ t in (0 : ℝ)..T, w t) ≤ T := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..T, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hT (hw.intervalIntegrable 0 T)
          (intervalIntegrable_const) (fun t ht => Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [ht.1]) ha))
      _ = T := by simp
  have hd (t : ℝ) : HasDerivAt (fun s => -(1 / 2 : ℝ) * w s) (a * w t) t := by
    have h := (((hasDerivAt_id t).const_mul (-2)).mul_const a).exp.const_mul (-(1 / 2 : ℝ))
    convert! h using 1
    simp only [id_eq]
    dsimp only [w]
    ring
  have hi : IntervalIntegrable (fun t => a * w t) volume 0 T :=
    (continuous_const.mul hw).intervalIntegrable 0 T
  have hg : (∫ t in (0 : ℝ)..T, a * w t) = (1 - w T) / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
    simp only [w, mul_zero, zero_mul, Real.exp_zero, mul_one]
    ring
  have hb : (∫ t in (0 : ℝ)..T, a * w t) ≤ 1 / 2 := by
    rw [hg]
    linarith [Real.exp_nonneg (-2 * T * a)]
  have heq (t : ℝ) : (Real.sqrt (1 + a) * Real.exp (-t * a) * c) ^ 2 =
      (w t + a * w t) * c ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + a)]
    have he : Real.exp (-t * a) ^ 2 = w t := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hw.intervalIntegrable 0 T) hi]
  exact mul_le_mul_of_nonneg_right (add_le_add hv hb) (sq_nonneg c)

theorem scalar_heat_form_lintegral {T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (c : ℝ) :
    (∫⁻ t, ENNReal.ofReal ((Real.sqrt (1 + a) * Real.exp (-t * a) * c) ^ 2)
      ∂timeMeasure T) ≤ ENNReal.ofReal (T + 1 / 2) * ENNReal.ofReal (c ^ 2) := by
  have hi : Integrable (fun t : ℝ => (Real.sqrt (1 + a) * Real.exp (-t * a) * c) ^ 2)
      (timeMeasure T) :=
    (show Continuous (fun t : ℝ => (Real.sqrt (1 + a) * Real.exp (-t * a) * c) ^ 2)
      by fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ENNReal.ofReal_mul (by linarith : 0 ≤ T + 1 / 2)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [intervalIntegral.integral_of_le hT] using scalar_heat_form_energy hT ha c

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
