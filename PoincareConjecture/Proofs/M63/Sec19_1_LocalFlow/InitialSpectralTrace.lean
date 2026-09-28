import PoincareConjecture.Proofs.M03.Existence.SpectralShiftedNative












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {iota : Type*} [Countable iota] (lambda : iota → NNReal) (w : State iota)





noncomputable def initialHeatGenerator (t : ℝ) : State iota :=
  stateOfCoeffs (fun i => (lambda i : ℝ) * Real.exp (-t * lambda i) *
    shiftedBaseMultiplier lambda w i)




theorem initialHeatGenerator_eq {t : ℝ} (ht : 0 < t) :
    initialHeatGenerator lambda w t =
      heatGenerator lambda t ht (shiftedBaseMultiplier lambda w) := by
  apply lp.ext
  funext i
  exact stateOfCoeffs_apply
    (lp.memℓp (heatGenerator lambda t ht (shiftedBaseMultiplier lambda w))) i




theorem initialHeatGenerator_memLp_energy {T : ℝ} (hT : 0 ≤ T) :
    MemLp (initialHeatGenerator lambda w) 2 (timeMeasure T) ∧
      (∫ t, ‖initialHeatGenerator lambda w t‖ ^ 2 ∂timeMeasure T) ≤ ‖w‖ ^ 2 / 2 := by
  let c := shiftedBaseMultiplier lambda w
  let a : ℝ → iota → ℝ := fun t i => (lambda i : ℝ) * Real.exp (-t * lambda i) * c i
  have ha (i : iota) : AEStronglyMeasurable (fun t => a t i) (timeMeasure T) :=
    (show Continuous (fun t => a t i) by dsimp [a]; fun_prop).aestronglyMeasurable
  have hscalar (i : iota) : (∫ t, a t i ^ 2 ∂timeMeasure T) ≤ w i ^ 2 / 2 := by
    have he := spectralMode_energy_le (lambda := (lambda i : ℝ)) (c := c i)
      (f := fun _ => 0) (lambda i).coe_nonneg hT continuousOn_const
    have hmode (t : ℝ) : spectralMode (lambda i) (c i) (fun _ => 0) t =
        Real.exp (-t * lambda i) * c i := by
      simp only [spectralMode, mul_zero, intervalIntegral.integral_zero, add_zero]
      congr 2
      ring
    simp only [hmode, zero_sub, neg_sq, zero_pow (by norm_num : 2 ≠ 0),
      intervalIntegral.integral_of_le hT, integral_zero, zero_add] at he
    have hweight : (1 + (lambda i : ℝ)) * c i ^ 2 = w i ^ 2 := by
      change (1 + (lambda i : ℝ)) *
        (1 / Real.sqrt (1 + (lambda i : ℝ)) * w i) ^ 2 = _
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
      field_simp
    have hbound : (lambda i : ℝ) * c i ^ 2 ≤ w i ^ 2 := by
      nlinarith [sq_nonneg (c i)]
    dsimp [a]
    simp only [timeMeasure, mul_assoc] at he ⊢
    linarith
  have henergy : (∫⁻ t, squareSum (a t) ∂timeMeasure T) ≤
      ENNReal.ofReal (‖w‖ ^ 2 / 2) := by
    calc
      _ = ∑' i, ∫⁻ t, ENNReal.ofReal (a t i ^ 2) ∂timeMeasure T :=
        lintegral_tsum (fun i => ((ha i).aemeasurable.pow_const 2).ennreal_ofReal)
      _ ≤ ∑' i, ENNReal.ofReal (w i ^ 2 / 2) := by
        apply ENNReal.tsum_le_tsum
        intro i
        have hi : Integrable (fun t => a t i ^ 2) (timeMeasure T) :=
          (show Continuous (fun t => a t i ^ 2) by dsimp [a]; fun_prop).continuousOn
            |>.integrableOn_Icc |>.mono_set Ioc_subset_Icc_self
        rw [← ofReal_integral_eq_lintegral_ofReal hi
          (Eventually.of_forall (fun _ => sq_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (hscalar i)
      _ = ENNReal.ofReal (1 / 2 : ℝ) * squareSum w := by
        simp only [div_eq_mul_inv, mul_comm (_ ^ 2) (2 : ℝ)⁻¹,
          ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)⁻¹),
          ENNReal.tsum_mul_left, squareSum, one_mul]
      _ = _ := by
        rw [squareSum_state, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
        congr 1
        ring
  have hfinite := henergy.trans_lt ENNReal.ofReal_lt_top
  refine ⟨memLp_stateOfCoeffs ha hfinite, ?_⟩
  change (∫ t, ‖stateOfCoeffs (a t)‖ ^ 2 ∂timeMeasure T) ≤ _
  rw [integral_sq_norm_stateOfCoeffs ha hfinite]
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ‖w‖ ^ 2 / 2)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top henergy




noncomputable def initialHeatHigh (t : ℝ) : State iota :=
  heat lambda t.toNNReal (shiftedBaseMultiplier lambda w) + initialHeatGenerator lambda w t




theorem initialHeatHigh_coeff {t : ℝ} (ht : 0 < t) (i : iota) :
    initialHeatHigh lambda w t i = (1 + (lambda i : ℝ)) * Real.exp (-t * lambda i) *
      shiftedBaseMultiplier lambda w i := by
  rw [initialHeatHigh, initialHeatGenerator_eq lambda w ht]
  simp only [lp.coeFn_add, Pi.add_apply, heat_apply, heatGenerator_apply,
    Real.coe_toNNReal t ht.le]
  ring




theorem initialHeatHigh_trace {t : ℝ} (ht : 0 < t) :
    shiftedBaseMultiplier lambda (initialHeatHigh lambda w t) = heat lambda t.toNNReal w ∧
      ‖shiftedBaseMultiplier lambda (initialHeatHigh lambda w t)‖ ≤ ‖w‖ := by
  have heq : shiftedBaseMultiplier lambda (initialHeatHigh lambda w t) =
      heat lambda t.toNNReal w := by
    apply lp.ext
    funext i
    change 1 / Real.sqrt (1 + (lambda i : ℝ)) * initialHeatHigh lambda w t i = _
    rw [initialHeatHigh_coeff lambda w ht, heat_apply, Real.coe_toNNReal t ht.le]
    change 1 / Real.sqrt (1 + (lambda i : ℝ)) *
      ((1 + (lambda i : ℝ)) * Real.exp (-t * lambda i) *
        (1 / Real.sqrt (1 + (lambda i : ℝ)) * w i)) = _
    have hp : 0 < 1 + (lambda i : ℝ) := by positivity
    have hs := Real.sq_sqrt hp.le
    field_simp
    rw [hs]
  exact ⟨heq, heq ▸ norm_heat_apply_le lambda t.toNNReal w⟩




theorem initialHeatHigh_memLp_energy {T : ℝ} (hT : 0 ≤ T) :
    MemLp (initialHeatHigh lambda w) 2 (timeMeasure T) ∧
      (∫ t, ‖initialHeatHigh lambda w t‖ ^ 2 ∂timeMeasure T) ≤ (2 * T + 1) * ‖w‖ ^ 2 := by
  let U : ℝ → State iota := fun t => heat lambda t.toNNReal (shiftedBaseMultiplier lambda w)
  have hUcont : Continuous U :=
    (continuous_heat_apply lambda (shiftedBaseMultiplier lambda w)).comp continuous_real_toNNReal
  have hUint : Integrable (fun t => ‖U t‖ ^ 2) (timeMeasure T) :=
    (hUcont.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hUmem : MemLp U 2 (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm hUcont.aestronglyMeasurable).mpr hUint
  have hUbound (t : ℝ) : ‖U t‖ ≤ ‖w‖ :=
    (norm_heat_apply_le lambda t.toNNReal (shiftedBaseMultiplier lambda w)).trans
      (norm_shiftedBaseMultiplier_le lambda w)
  have hUenergy : (∫ t, ‖U t‖ ^ 2 ∂timeMeasure T) ≤ T * ‖w‖ ^ 2 := by
    calc
      _ ≤ ∫ _t, ‖w‖ ^ 2 ∂timeMeasure T :=
        integral_mono_ae hUint (integrable_const _) (Eventually.of_forall (fun t =>
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hUbound t)))
      _ = _ := by
        simp [timeMeasure, integral_const, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal hT, smul_eq_mul]
  obtain ⟨hGmem, hGenergy⟩ := initialHeatGenerator_memLp_energy lambda w hT
  have hGint := (memLp_two_iff_integrable_sq_norm hGmem.aestronglyMeasurable).mp hGmem
  have hHmem : MemLp (initialHeatHigh lambda w) 2 (timeMeasure T) := hUmem.add hGmem
  refine ⟨hHmem, ?_⟩
  calc
    _ ≤ ∫ t, 2 * ‖U t‖ ^ 2 + 2 * ‖initialHeatGenerator lambda w t‖ ^ 2 ∂timeMeasure T := by
      apply integral_mono_ae
        ((memLp_two_iff_integrable_sq_norm hHmem.aestronglyMeasurable).mp hHmem)
        ((hUint.const_mul 2).add (hGint.const_mul 2))
      exact Eventually.of_forall (fun t => by
        have hn := pow_le_pow_left₀ (norm_nonneg (U t + initialHeatGenerator lambda w t))
          (norm_add_le (U t) (initialHeatGenerator lambda w t)) 2
        change ‖U t + initialHeatGenerator lambda w t‖ ^ 2 ≤
          2 * ‖U t‖ ^ 2 + 2 * ‖initialHeatGenerator lambda w t‖ ^ 2
        nlinarith [sq_nonneg (‖U t‖ - ‖initialHeatGenerator lambda w t‖)])
    _ = 2 * (∫ t, ‖U t‖ ^ 2 ∂timeMeasure T) +
        2 * (∫ t, ‖initialHeatGenerator lambda w t‖ ^ 2 ∂timeMeasure T) := by
      rw [integral_add (hUint.const_mul 2) (hGint.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by nlinarith





theorem initialHeat_eq_sub_integral {t : ℝ} (ht : 0 ≤ t) :
    heat lambda t.toNNReal (shiftedBaseMultiplier lambda w) =
      shiftedBaseMultiplier lambda w - ∫ s in (0 : ℝ)..t, initialHeatGenerator lambda w s := by
  have hGmem := (initialHeatGenerator_memLp_energy lambda w ht).1
  have hGint : IntervalIntegrable (initialHeatGenerator lambda w) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
      (hGmem.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  apply lp.ext
  funext i
  change heat lambda t.toNNReal (shiftedBaseMultiplier lambda w) i =
    shiftedBaseMultiplier lambda w i - (∫ s in (0 : ℝ)..t, initialHeatGenerator lambda w s) i
  have heval : (∫ s in (0 : ℝ)..t, initialHeatGenerator lambda w s) i =
      ∫ s in (0 : ℝ)..t, initialHeatGenerator lambda w s i :=
    ((lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).intervalIntegral_comp_comm hGint).symm
  rw [heat_apply, Real.coe_toNNReal t ht, heval]
  have hcoeff : (∫ s in (0 : ℝ)..t, initialHeatGenerator lambda w s i) =
      ∫ s in (0 : ℝ)..t,
        (lambda i : ℝ) * Real.exp (-s * lambda i) * shiftedBaseMultiplier lambda w i := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [initialHeatGenerator_eq lambda w hs.1]
    rfl
  rw [hcoeff]
  have hscalar := spectralMode_eq_initial_add_integral_defect
    (lambda := (lambda i : ℝ)) (c := shiftedBaseMultiplier lambda w i)
    (f := fun _ => 0) (T := t) intervalIntegrable_const right_mem_uIcc
  have hmode (s : ℝ) :
      spectralMode (lambda i) (shiftedBaseMultiplier lambda w i) (fun _ => 0) s =
        Real.exp (-s * lambda i) * shiftedBaseMultiplier lambda w i := by
    simp only [spectralMode, mul_zero, intervalIntegral.integral_zero, add_zero]
    congr 2
    ring
  simpa only [hmode, sub_eq_add_neg, zero_add, intervalIntegral.integral_neg, mul_assoc]
    using hscalar

end PoincareConjecture.M63
