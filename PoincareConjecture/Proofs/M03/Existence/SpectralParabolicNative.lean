import PoincareConjecture.Proofs.M03.Existence.SpectralEnergyNative
import PoincareConjecture.Proofs.M03.Existence.SpectralModeNative










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*}

abbrev timeMeasure (T : ℝ) : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)


def responseCoeff (lambda : iota → NNReal) (F : ℝ → State iota)
    (t : ℝ) (i : iota) : ℝ :=
  spectralMode (lambda i) 0 (fun s => F s i) t

def generatorCoeff (lambda : iota → NNReal) (F : ℝ → State iota)
    (t : ℝ) (i : iota) : ℝ :=
  (lambda i : ℝ) * responseCoeff lambda F t i

def derivativeCoeff (lambda : iota → NNReal) (F : ℝ → State iota)
    (t : ℝ) (i : iota) : ℝ :=
  F t i - generatorCoeff lambda F t i

theorem continuousOn_coordinate {T : ℝ} {F : ℝ → State iota}
    (hF : ContinuousOn F (Icc (0 : ℝ) T)) (i : iota) :
    ContinuousOn (fun t => F t i) (Icc (0 : ℝ) T) :=
  (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.comp_continuousOn hF

theorem continuousOn_responseCoeff {T : ℝ} {F : ℝ → State iota}
    (hF : ContinuousOn F (Icc (0 : ℝ) T)) (lambda : iota → NNReal) (i : iota) :
    ContinuousOn (fun t => responseCoeff lambda F t i) (Icc (0 : ℝ) T) :=
  continuousOn_spectralMode (continuousOn_coordinate hF i)

theorem continuousOn_generatorCoeff {T : ℝ} {F : ℝ → State iota}
    (hF : ContinuousOn F (Icc (0 : ℝ) T)) (lambda : iota → NNReal) (i : iota) :
    ContinuousOn (fun t => generatorCoeff lambda F t i) (Icc (0 : ℝ) T) :=
  continuousOn_const.mul (continuousOn_responseCoeff hF lambda i)

theorem continuousOn_derivativeCoeff {T : ℝ} {F : ℝ → State iota}
    (hF : ContinuousOn F (Icc (0 : ℝ) T)) (lambda : iota → NNReal) (i : iota) :
    ContinuousOn (fun t => derivativeCoeff lambda F t i) (Icc (0 : ℝ) T) :=
  (continuousOn_coordinate hF i).sub (continuousOn_generatorCoeff hF lambda i)

private theorem scalar_lintegral_energy_le {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) (i : iota) :
    (∫⁻ t, ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2) ∂timeMeasure T) +
        (∫⁻ t, ENNReal.ofReal (generatorCoeff lambda F t i ^ 2) ∂timeMeasure T) ≤
      ∫⁻ t, ENNReal.ofReal (F t i ^ 2) ∂timeMeasure T := by
  have hD : Integrable (fun t => derivativeCoeff lambda F t i ^ 2) (timeMeasure T) :=
    ((continuousOn_derivativeCoeff hF lambda i).pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hA : Integrable (fun t => generatorCoeff lambda F t i ^ 2) (timeMeasure T) :=
    ((continuousOn_generatorCoeff hF lambda i).pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hR : Integrable (fun t => F t i ^ 2) (timeMeasure T) :=
    ((continuousOn_coordinate hF i).pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hA (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hR (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ENNReal.ofReal_add (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  simpa only [derivativeCoeff, generatorCoeff, responseCoeff,
    intervalIntegral.integral_of_le hT, sq, mul_zero, add_zero] using
    spectralMode_energy_le (c := 0) (lambda i).coe_nonneg hT
      (continuousOn_coordinate hF i)



theorem lintegral_response_energy_le [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    (∫⁻ t, squareSum (derivativeCoeff lambda F t) ∂timeMeasure T) +
        (∫⁻ t, squareSum (generatorCoeff lambda F t) ∂timeMeasure T) ≤
      ∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂timeMeasure T := by
  have hD (i : iota) : AEMeasurable
      (fun t => ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2)) (timeMeasure T) :=
    ((((continuousOn_derivativeCoeff hF lambda i).pow 2).mono Ioc_subset_Icc_self).aemeasurable
      measurableSet_Ioc).ennreal_ofReal
  have hA (i : iota) : AEMeasurable
      (fun t => ENNReal.ofReal (generatorCoeff lambda F t i ^ 2)) (timeMeasure T) :=
    ((((continuousOn_generatorCoeff hF lambda i).pow 2).mono Ioc_subset_Icc_self).aemeasurable
      measurableSet_Ioc).ennreal_ofReal
  have hR (i : iota) : AEMeasurable
      (fun t => ENNReal.ofReal (F t i ^ 2)) (timeMeasure T) :=
    ((((continuousOn_coordinate hF i).pow 2).mono Ioc_subset_Icc_self).aemeasurable
      measurableSet_Ioc).ennreal_ofReal
  calc
    _ = (∑' i, ∫⁻ t, ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2) ∂timeMeasure T) +
        (∑' i, ∫⁻ t, ENNReal.ofReal (generatorCoeff lambda F t i ^ 2) ∂timeMeasure T) := by
      simp only [squareSum]
      rw [lintegral_tsum hD, lintegral_tsum hA]
    _ = ∑' i, ((∫⁻ t, ENNReal.ofReal (derivativeCoeff lambda F t i ^ 2) ∂timeMeasure T) +
        (∫⁻ t, ENNReal.ofReal (generatorCoeff lambda F t i ^ 2) ∂timeMeasure T)) :=
      ENNReal.tsum_add.symm
    _ ≤ ∑' i, ∫⁻ t, ENNReal.ofReal (F t i ^ 2) ∂timeMeasure T :=
      ENNReal.tsum_le_tsum (scalar_lintegral_energy_le hT hF lambda)
    _ = ∫⁻ t, squareSum (F t) ∂timeMeasure T := (lintegral_tsum hR).symm
    _ = _ := by simp only [squareSum_state]

theorem forcing_energy_lt_top {T : ℝ} {F : ℝ → State iota}
    (hF : ContinuousOn F (Icc (0 : ℝ) T)) :
    (∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂timeMeasure T) < ∞ := by
  have hi : Integrable (fun t => ‖F t‖ ^ 2) (timeMeasure T) :=
    (hF.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_lt_top

def generatorState (lambda : iota → NNReal) (F : ℝ → State iota) (t : ℝ) : State iota :=
  stateOfCoeffs (generatorCoeff lambda F t)

def derivativeState (lambda : iota → NNReal) (F : ℝ → State iota) (t : ℝ) : State iota :=
  stateOfCoeffs (derivativeCoeff lambda F t)

theorem generator_energy_lt_top [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    (∫⁻ t, squareSum (generatorCoeff lambda F t) ∂timeMeasure T) < ∞ :=
  lt_of_le_of_lt ((le_add_left le_rfl).trans (lintegral_response_energy_le hT hF lambda))
    (forcing_energy_lt_top hF)

theorem derivative_energy_lt_top [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    (∫⁻ t, squareSum (derivativeCoeff lambda F t) ∂timeMeasure T) < ∞ :=
  lt_of_le_of_lt ((le_add_right le_rfl).trans (lintegral_response_energy_le hT hF lambda))
    (forcing_energy_lt_top hF)

theorem memLp_generatorState [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) : MemLp (generatorState lambda F) 2 (timeMeasure T) :=
  memLp_stateOfCoeffs (fun i =>
    ((continuousOn_generatorCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) (generator_energy_lt_top hT hF lambda)

theorem memLp_derivativeState [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) : MemLp (derivativeState lambda F) 2 (timeMeasure T) :=
  memLp_stateOfCoeffs (fun i =>
    ((continuousOn_derivativeCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) (derivative_energy_lt_top hT hF lambda)



theorem derivativeState_add_generatorState [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    ∀ᵐ t ∂timeMeasure T, derivativeState lambda F t + generatorState lambda F t = F t := by
  have hD := ae_memℓp_of_lintegral_squareSum_lt_top (fun i =>
    ((continuousOn_derivativeCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) (derivative_energy_lt_top hT hF lambda)
  have hA := ae_memℓp_of_lintegral_squareSum_lt_top (fun i =>
    ((continuousOn_generatorCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) (generator_energy_lt_top hT hF lambda)
  filter_upwards [hD, hA] with t htD htA
  apply lp.ext
  funext i
  change stateOfCoeffs (derivativeCoeff lambda F t) i +
    stateOfCoeffs (generatorCoeff lambda F t) i = F t i
  rw [stateOfCoeffs_apply htD, stateOfCoeffs_apply htA]
  exact sub_add_cancel _ _


theorem integral_response_energy_le [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (lambda : iota → NNReal) :
    (∫ t, ‖derivativeState lambda F t‖ ^ 2 ∂timeMeasure T) +
        (∫ t, ‖generatorState lambda F t‖ ^ 2 ∂timeMeasure T) ≤
      ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  have hD := derivative_energy_lt_top hT hF lambda
  have hA := generator_energy_lt_top hT hF lambda
  have hR := forcing_energy_lt_top hF
  have he := ENNReal.toReal_mono hR.ne (lintegral_response_energy_le hT hF lambda)
  rw [ENNReal.toReal_add hD.ne hA.ne] at he
  have hd := integral_sq_norm_stateOfCoeffs (fun i =>
    ((continuousOn_derivativeCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) hD
  have ha := integral_sq_norm_stateOfCoeffs (fun i =>
    ((continuousOn_generatorCoeff hF lambda i).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) hA
  have hi : Integrable (fun t => ‖F t‖ ^ 2) (timeMeasure T) :=
    (hF.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hr := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun _ => sq_nonneg _))
  have hn : 0 ≤ ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := integral_nonneg (fun _ => sq_nonneg _)
  rw [← hd, ← ha, ← hr, ENNReal.toReal_ofReal hn] at he
  exact he

end PoincareConjecture.SpectralHeatNative
