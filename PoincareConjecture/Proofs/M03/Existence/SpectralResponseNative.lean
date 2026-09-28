import PoincareConjecture.Proofs.M03.Existence.SpectralParabolicNative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm











set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*}


def responseState (lambda : iota → NNReal) (F : ℝ → State iota) (t : ℝ) : State iota :=
  ∫ s in (0 : ℝ)..t, derivativeState lambda F s

@[simp] theorem responseState_zero (lambda : iota → NNReal) (F : ℝ → State iota) :
    responseState lambda F 0 = 0 := by
  simp [responseState]

theorem intervalIntegrable_derivativeState [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    IntervalIntegrable (derivativeState lambda F) volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    (memLp_derivativeState hT hF lambda)

theorem continuousOn_responseState [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    ContinuousOn (responseState lambda F) (Icc (0 : ℝ) T) := by
  change ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, derivativeState lambda F s)
    (Icc (0 : ℝ) T)
  simpa only [uIcc_of_le hT] using
    intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_derivativeState hT hF lambda) left_mem_uIcc

theorem ae_derivativeState_apply [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T, ∀ i, derivativeState lambda F t i = derivativeCoeff lambda F t i := by
  have hm := ae_memℓp_of_lintegral_squareSum_lt_top (fun i =>
    ((continuousOn_derivativeCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) (derivative_energy_lt_top hT hF lambda)
  filter_upwards [hm] with t ht
  intro i
  exact stateOfCoeffs_apply ht i


theorem responseState_apply [Countable iota] {T t : ℝ}
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) (ht : t ∈ Icc (0 : ℝ) T) (i : iota) :
    responseState lambda F t i = responseCoeff lambda F t i := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hD := intervalIntegrable_derivativeState hT hF lambda
  have hDt : IntervalIntegrable (derivativeState lambda F) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hD).mono_set
      (Ioc_subset_Ioc le_rfl ht.2)
  have hcoeff : (fun s => derivativeState lambda F s i) =ᵐ[timeMeasure t]
      (fun s => derivativeCoeff lambda F s i) :=
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
      (ae_derivativeState_apply hT hF lambda)).mono (fun s hs => hs i)
  have hf := (continuousOn_coordinate hF i).mono (Icc_subset_Icc le_rfl ht.2)
  have hDI : IntervalIntegrable (fun s => derivativeCoeff lambda F s i) volume 0 t :=
    ((continuousOn_derivativeCoeff hF lambda i).mono
      (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (continuousOn_spectralMode (lambda := (lambda i : ℝ)) (c := 0) hf)
    (fun s hs => hasDerivAt_spectralMode_of_mem_Ioo hf hs) hDI
  calc
    responseState lambda F t i = ∫ s in (0 : ℝ)..t, derivativeState lambda F s i :=
      ((lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).intervalIntegral_comp_comm hDt).symm
    _ = ∫ s in (0 : ℝ)..t, derivativeCoeff lambda F s i := by
      apply intervalIntegral.integral_congr_ae_restrict
      simpa only [uIoc_of_le ht.1] using hcoeff
    _ = responseCoeff lambda F t i := by
      simpa only [derivativeCoeff, generatorCoeff, responseCoeff,
        spectralMode_zero, sub_zero] using hftc

theorem ae_hasDerivAt_responseState [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (responseState lambda F) (derivativeState lambda F t) t := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [(intervalIntegrable_derivativeState hT hF lambda).ae_hasDerivAt_integral]
    with t ht hmem
  exact ht (by simpa only [uIcc_of_le hT] using Ioc_subset_Icc_self hmem) 0 left_mem_uIcc


theorem ae_generatorState_apply [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      generatorState lambda F t i = (lambda i : ℝ) * responseState lambda F t i := by
  have hm := ae_memℓp_of_lintegral_squareSum_lt_top (fun i =>
    ((continuousOn_generatorCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) (generator_energy_lt_top hT hF lambda)
  filter_upwards [hm, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  intro i
  change stateOfCoeffs (generatorCoeff lambda F t) i = _
  rw [stateOfCoeffs_apply ht, responseState_apply hF lambda (Ioc_subset_Icc_self hmem)]
  rfl


theorem ae_responseState_equation [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (responseState lambda F) (F t - generatorState lambda F t) t := by
  filter_upwards [ae_hasDerivAt_responseState hT hF lambda,
    derivativeState_add_generatorState hT hF lambda] with t ht heq
  exact ht.congr_deriv (eq_sub_iff_add_eq.mpr heq)


theorem exists_spectralHeat_response [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    (lambda : iota → NNReal) {F : ℝ → State iota}
    (hF : ContinuousOn F (Icc (0 : ℝ) T)) :
    ∃ U D G : ℝ → State iota,
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (timeMeasure T) ∧ MemLp G 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + G t = F t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i, G t i = (lambda i : ℝ) * U t i) ∧
      (∫ t, ‖D t‖ ^ 2 ∂timeMeasure T) + (∫ t, ‖G t‖ ^ 2 ∂timeMeasure T) ≤
        ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  exact ⟨responseState lambda F, derivativeState lambda F, generatorState lambda F,
    responseState_zero lambda F, continuousOn_responseState hT hF lambda,
    memLp_derivativeState hT hF lambda, memLp_generatorState hT hF lambda,
    ae_hasDerivAt_responseState hT hF lambda, derivativeState_add_generatorState hT hF lambda,
    ae_generatorState_apply hT hF lambda, integral_response_energy_le hT hF lambda⟩

end PoincareConjecture.SpectralHeatNative
