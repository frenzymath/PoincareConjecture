import PoincareConjecture.Proofs.M03.Existence.SpectralResponseNative
import PoincareConjecture.Proofs.M03.Existence.SpectralModeStateNative










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*}

theorem memLp_coordinate {μ : Measure ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 μ) (i : iota) : MemLp (fun t => F t i) 2 μ :=
  hF.continuousLinearMap_comp (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i)

theorem continuousOn_responseCoeff_of_memLp {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (i : iota) :
    ContinuousOn (fun t => responseCoeff lambda F t i) (Icc (0 : ℝ) T) := by
  have hfi := (intervalIntegrable_and_sq_of_memLp_two hT (memLp_coordinate hF i)).1
  simpa only [responseCoeff, uIcc_of_le hT] using
    (absolutelyContinuousOnInterval_spectralMode
      (lambda := (lambda i : ℝ)) (c := 0) hfi).continuousOn

theorem continuousOn_generatorCoeff_of_memLp {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (i : iota) :
    ContinuousOn (fun t => generatorCoeff lambda F t i) (Icc (0 : ℝ) T) :=
  continuousOn_const.mul (continuousOn_responseCoeff_of_memLp hT hF lambda i)

theorem aestronglyMeasurable_generatorCoeff_of_memLp {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (i : iota) :
    AEStronglyMeasurable (fun t => generatorCoeff lambda F t i) (timeMeasure T) :=
  ((continuousOn_generatorCoeff_of_memLp hT hF lambda i).mono
    Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc

theorem aestronglyMeasurable_derivativeCoeff_of_memLp {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (i : iota) :
    AEStronglyMeasurable (fun t => derivativeCoeff lambda F t i) (timeMeasure T) :=
  (memLp_coordinate hF i).aestronglyMeasurable.sub
    (aestronglyMeasurable_generatorCoeff_of_memLp hT hF lambda i)

private theorem scalar_lintegral_energy_le_of_memLp {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (i : iota) :
    (∫⁻ t, ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2) ∂timeMeasure T) +
        (∫⁻ t, ENNReal.ofReal (generatorCoeff lambda F t i ^ 2) ∂timeMeasure T) ≤
      ∫⁻ t, ENNReal.ofReal (F t i ^ 2) ∂timeMeasure T := by
  have hcoord := memLp_coordinate hF i
  obtain ⟨hfi, hfi2⟩ := intervalIntegrable_and_sq_of_memLp_two hT hcoord
  have hD : Integrable (fun t => derivativeCoeff lambda F t i ^ 2) (timeMeasure T) :=
    (intervalIntegrable_spectralMode_defect_sq
      (lambda := (lambda i : ℝ)) (c := 0) hfi hfi2).1
  have hA : Integrable (fun t => generatorCoeff lambda F t i ^ 2) (timeMeasure T) :=
    ((continuousOn_generatorCoeff_of_memLp hT hF lambda i).pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hR : Integrable (fun t => F t i ^ 2) (timeMeasure T) := hcoord.integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hA (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hR (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ENNReal.ofReal_add (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have he := spectralMode_energy_identity_of_memLp
    (lambda := (lambda i : ℝ)) (c := 0) hT hcoord
  have htrace : 0 ≤ (lambda i : ℝ) *
      spectralMode (lambda i) 0 (fun s => F s i) T ^ 2 :=
    mul_nonneg (lambda i).coe_nonneg (sq_nonneg _)
  have hsum :
      (∫ t in (0 : ℝ)..T,
        (F t i - (lambda i : ℝ) * spectralMode (lambda i) 0 (fun s => F s i) t) ^ 2) +
      (∫ t in (0 : ℝ)..T,
        ((lambda i : ℝ) * spectralMode (lambda i) 0 (fun s => F s i) t) ^ 2) ≤
        ∫ t in (0 : ℝ)..T, F t i ^ 2 := by
    nlinarith
  simpa only [derivativeCoeff, generatorCoeff, responseCoeff,
    intervalIntegral.integral_of_le hT] using hsum


theorem lintegral_response_energy_le_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    (∫⁻ t, squareSum (derivativeCoeff lambda F t) ∂timeMeasure T) +
        (∫⁻ t, squareSum (generatorCoeff lambda F t) ∂timeMeasure T) ≤
      ∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂timeMeasure T := by
  have hD (i : iota) : AEMeasurable
      (fun t => ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2)) (timeMeasure T) :=
    ((aestronglyMeasurable_derivativeCoeff_of_memLp hT hF lambda i).aemeasurable.pow_const 2).ennreal_ofReal
  have hA (i : iota) : AEMeasurable
      (fun t => ENNReal.ofReal (generatorCoeff lambda F t i ^ 2)) (timeMeasure T) :=
    ((aestronglyMeasurable_generatorCoeff_of_memLp hT hF lambda i).aemeasurable.pow_const 2).ennreal_ofReal
  have hR (i : iota) : AEMeasurable
      (fun t => ENNReal.ofReal (F t i ^ 2)) (timeMeasure T) :=
    ((memLp_coordinate hF i).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  calc
    _ = (∑' i, ∫⁻ t, ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2) ∂timeMeasure T) +
        (∑' i, ∫⁻ t, ENNReal.ofReal (generatorCoeff lambda F t i ^ 2) ∂timeMeasure T) := by
      simp only [squareSum]
      rw [lintegral_tsum hD, lintegral_tsum hA]
    _ = ∑' i, ((∫⁻ t, ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2) ∂timeMeasure T) +
        (∫⁻ t, ENNReal.ofReal (generatorCoeff lambda F t i ^ 2) ∂timeMeasure T)) :=
      ENNReal.tsum_add.symm
    _ ≤ ∑' i, ∫⁻ t, ENNReal.ofReal (F t i ^ 2) ∂timeMeasure T :=
      ENNReal.tsum_le_tsum (scalar_lintegral_energy_le_of_memLp hT hF lambda)
    _ = ∫⁻ t, squareSum (F t) ∂timeMeasure T := (lintegral_tsum hR).symm
    _ = _ := by simp only [squareSum_state]

theorem forcing_energy_lt_top_of_memLp {T : ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) :
    (∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂timeMeasure T) < ∞ := by
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_lt_top

theorem generator_energy_lt_top_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    (∫⁻ t, squareSum (generatorCoeff lambda F t) ∂timeMeasure T) < ∞ :=
  lt_of_le_of_lt
    ((le_add_left le_rfl).trans (lintegral_response_energy_le_of_memLp hT hF lambda))
    (forcing_energy_lt_top_of_memLp hF)

theorem derivative_energy_lt_top_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    (∫⁻ t, squareSum (derivativeCoeff lambda F t) ∂timeMeasure T) < ∞ :=
  lt_of_le_of_lt
    ((le_add_right le_rfl).trans (lintegral_response_energy_le_of_memLp hT hF lambda))
    (forcing_energy_lt_top_of_memLp hF)

theorem memLp_generatorState_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) : MemLp (generatorState lambda F) 2 (timeMeasure T) :=
  memLp_stateOfCoeffs (aestronglyMeasurable_generatorCoeff_of_memLp hT hF lambda)
    (generator_energy_lt_top_of_memLp hT hF lambda)

theorem memLp_derivativeState_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) : MemLp (derivativeState lambda F) 2 (timeMeasure T) :=
  memLp_stateOfCoeffs (aestronglyMeasurable_derivativeCoeff_of_memLp hT hF lambda)
    (derivative_energy_lt_top_of_memLp hT hF lambda)

theorem intervalIntegrable_derivativeState_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    IntervalIntegrable (derivativeState lambda F) volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    (memLp_derivativeState_of_memLp hT hF lambda)

theorem continuousOn_responseState_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    ContinuousOn (responseState lambda F) (Icc (0 : ℝ) T) := by
  change ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, derivativeState lambda F s)
    (Icc (0 : ℝ) T)
  simpa only [uIcc_of_le hT] using
    intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_derivativeState_of_memLp hT hF lambda) left_mem_uIcc

theorem ae_derivativeState_apply_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T, ∀ i, derivativeState lambda F t i = derivativeCoeff lambda F t i := by
  have hm := ae_memℓp_of_lintegral_squareSum_lt_top
    (aestronglyMeasurable_derivativeCoeff_of_memLp hT hF lambda)
    (derivative_energy_lt_top_of_memLp hT hF lambda)
  filter_upwards [hm] with t ht
  intro i
  exact stateOfCoeffs_apply ht i


theorem responseState_apply_of_memLp [Countable iota] {T t : ℝ}
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (ht : t ∈ Icc (0 : ℝ) T) (i : iota) :
    responseState lambda F t i = responseCoeff lambda F t i := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hD := intervalIntegrable_derivativeState_of_memLp hT hF lambda
  have hDt : IntervalIntegrable (derivativeState lambda F) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hD).mono_set
      (Ioc_subset_Ioc le_rfl ht.2)
  have hcoeff : (fun s => derivativeState lambda F s i) =ᵐ[timeMeasure t]
      (fun s => derivativeCoeff lambda F s i) :=
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
      (ae_derivativeState_apply_of_memLp hT hF lambda)).mono (fun s hs => hs i)
  have hfi := (intervalIntegrable_and_sq_of_memLp_two hT (memLp_coordinate hF i)).1
  have hscalar := spectralMode_eq_initial_add_integral_defect
    (lambda := (lambda i : ℝ)) (c := 0) hfi (by simpa only [uIcc_of_le hT] using ht)
  calc
    responseState lambda F t i = ∫ s in (0 : ℝ)..t, derivativeState lambda F s i :=
      ((lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).intervalIntegral_comp_comm hDt).symm
    _ = ∫ s in (0 : ℝ)..t, derivativeCoeff lambda F s i := by
      apply intervalIntegral.integral_congr_ae_restrict
      simpa only [uIoc_of_le ht.1] using hcoeff
    _ = responseCoeff lambda F t i := by
      simpa only [derivativeCoeff, generatorCoeff, responseCoeff, zero_add] using hscalar.symm

theorem ae_hasDerivAt_responseState_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (responseState lambda F) (derivativeState lambda F t) t := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hD := intervalIntegrable_derivativeState_of_memLp hT hF lambda
  filter_upwards [hD.ae_hasDerivAt_integral] with t ht hmem
  exact ht (by simpa only [uIcc_of_le hT] using Ioc_subset_Icc_self hmem) 0 left_mem_uIcc

theorem derivativeState_add_generatorState_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T, derivativeState lambda F t + generatorState lambda F t = F t := by
  have hD := ae_memℓp_of_lintegral_squareSum_lt_top
    (aestronglyMeasurable_derivativeCoeff_of_memLp hT hF lambda)
    (derivative_energy_lt_top_of_memLp hT hF lambda)
  have hA := ae_memℓp_of_lintegral_squareSum_lt_top
    (aestronglyMeasurable_generatorCoeff_of_memLp hT hF lambda)
    (generator_energy_lt_top_of_memLp hT hF lambda)
  filter_upwards [hD, hA] with t htD htA
  apply lp.ext
  funext i
  change stateOfCoeffs (derivativeCoeff lambda F t) i +
    stateOfCoeffs (generatorCoeff lambda F t) i = F t i
  rw [stateOfCoeffs_apply htD, stateOfCoeffs_apply htA]
  exact sub_add_cancel _ _


theorem ae_generatorState_apply_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      generatorState lambda F t i = (lambda i : ℝ) * responseState lambda F t i := by
  have hm := ae_memℓp_of_lintegral_squareSum_lt_top
    (aestronglyMeasurable_generatorCoeff_of_memLp hT hF lambda)
    (generator_energy_lt_top_of_memLp hT hF lambda)
  filter_upwards [hm, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  intro i
  change stateOfCoeffs (generatorCoeff lambda F t) i = _
  rw [stateOfCoeffs_apply ht,
    responseState_apply_of_memLp hF lambda (Ioc_subset_Icc_self hmem)]
  rfl

theorem ae_responseState_equation_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (responseState lambda F) (F t - generatorState lambda F t) t := by
  filter_upwards [ae_hasDerivAt_responseState_of_memLp hT hF lambda,
    derivativeState_add_generatorState_of_memLp hT hF lambda] with t ht heq
  exact ht.congr_deriv (eq_sub_iff_add_eq.mpr heq)


theorem integral_response_energy_le_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    (∫ t, ‖derivativeState lambda F t‖ ^ 2 ∂timeMeasure T) +
        (∫ t, ‖generatorState lambda F t‖ ^ 2 ∂timeMeasure T) ≤
      ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  have hD := derivative_energy_lt_top_of_memLp hT hF lambda
  have hA := generator_energy_lt_top_of_memLp hT hF lambda
  have hR := forcing_energy_lt_top_of_memLp hF
  have he := ENNReal.toReal_mono hR.ne (lintegral_response_energy_le_of_memLp hT hF lambda)
  rw [ENNReal.toReal_add hD.ne hA.ne] at he
  have hd := integral_sq_norm_stateOfCoeffs
    (aestronglyMeasurable_derivativeCoeff_of_memLp hT hF lambda) hD
  have ha := integral_sq_norm_stateOfCoeffs
    (aestronglyMeasurable_generatorCoeff_of_memLp hT hF lambda) hA
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hr := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun _ => sq_nonneg _))
  have hn : 0 ≤ ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := integral_nonneg (fun _ => sq_nonneg _)
  rw [← hd, ← ha, ← hr, ENNReal.toReal_ofReal hn] at he
  exact he


theorem exists_spectralHeat_response_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    (lambda : iota → NNReal) {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) :
    ∃ U D G : ℝ → State iota,
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (timeMeasure T) ∧ MemLp G 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + G t = F t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i, G t i = (lambda i : ℝ) * U t i) ∧
      (∫ t, ‖D t‖ ^ 2 ∂timeMeasure T) + (∫ t, ‖G t‖ ^ 2 ∂timeMeasure T) ≤
        ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  exact ⟨responseState lambda F, derivativeState lambda F, generatorState lambda F,
    responseState_zero lambda F, continuousOn_responseState_of_memLp hT hF lambda,
    memLp_derivativeState_of_memLp hT hF lambda, memLp_generatorState_of_memLp hT hF lambda,
    ae_hasDerivAt_responseState_of_memLp hT hF lambda,
    derivativeState_add_generatorState_of_memLp hT hF lambda,
    ae_generatorState_apply_of_memLp hT hF lambda,
    integral_response_energy_le_of_memLp hT hF lambda⟩

end PoincareConjecture.SpectralHeatNative
