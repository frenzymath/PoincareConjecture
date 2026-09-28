import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.ScalarEnergy

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {ι : Type*}

def initialFormCoeffs (lambda : ι → NNReal) (x : State ι) (t : ℝ) (i : ι) : ℝ :=
  Real.sqrt (1 + (lambda i : ℝ)) * Real.exp (-t * lambda i) * x i

def initialFormState (lambda : ι → NNReal) (x : State ι) (t : ℝ) : State ι :=
  stateOfCoeffs (initialFormCoeffs lambda x t)

theorem initialFormCoeffs_continuous (lambda : ι → NNReal) (x : State ι) (i : ι) :
    Continuous (fun t => initialFormCoeffs lambda x t i) := by
  unfold initialFormCoeffs
  fun_prop

theorem initialForm_energy [Countable ι] (lambda : ι → NNReal) (x : State ι)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ t, squareSum (initialFormCoeffs lambda x t) ∂timeMeasure T) ≤
      ENNReal.ofReal (T + 1 / 2) * ENNReal.ofReal (‖x‖ ^ 2) := by
  have hm (i : ι) : AEMeasurable
      (fun t => ENNReal.ofReal (initialFormCoeffs lambda x t i ^ 2)) (timeMeasure T) :=
    ((initialFormCoeffs_continuous lambda x i).measurable.pow_const 2).ennreal_ofReal.aemeasurable
  calc
    _ = ∑' i, ∫⁻ t, ENNReal.ofReal (initialFormCoeffs lambda x t i ^ 2)
        ∂timeMeasure T := lintegral_tsum hm
    _ ≤ ∑' i, ENNReal.ofReal (T + 1 / 2) * ENNReal.ofReal (x i ^ 2) :=
      ENNReal.tsum_le_tsum (fun i => scalar_heat_form_lintegral hT (lambda i).coe_nonneg (x i))
    _ = _ := by rw [ENNReal.tsum_mul_left, ← squareSum, squareSum_state]

theorem initialForm_energy_lt_top [Countable ι] (lambda : ι → NNReal) (x : State ι)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ t, squareSum (initialFormCoeffs lambda x t) ∂timeMeasure T) < ∞ :=
  (initialForm_energy lambda x hT).trans_lt (by finiteness)

theorem initialFormState_memLp [Countable ι] (lambda : ι → NNReal) (x : State ι)
    {T : ℝ} (hT : 0 ≤ T) : MemLp (initialFormState lambda x) 2 (timeMeasure T) :=
  memLp_stateOfCoeffs
    (fun i => (initialFormCoeffs_continuous lambda x i).aestronglyMeasurable)
    (initialForm_energy_lt_top lambda x hT)

theorem initialFormState_coeff [Countable ι] (lambda : ι → NNReal) (x : State ι)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂timeMeasure T, ∀ i, initialFormState lambda x t i =
      Real.sqrt (1 + (lambda i : ℝ)) * Real.exp (-t * lambda i) * x i := by
  filter_upwards [ae_memℓp_of_lintegral_squareSum_lt_top
    (fun i => (initialFormCoeffs_continuous lambda x i).aestronglyMeasurable)
    (initialForm_energy_lt_top lambda x hT)] with t ht
  intro i
  exact stateOfCoeffs_apply ht i

def initialValueState (lambda : ι → NNReal) (x : State ι) (t : ℝ) : State ι :=
  heat lambda (Real.toNNReal t) x

theorem initialValueState_continuous (lambda : ι → NNReal) (x : State ι) :
    Continuous (initialValueState lambda x) := by
  exact (continuous_heat_apply lambda x).comp (by fun_prop)

theorem initialValueState_zero (lambda : ι → NNReal) (x : State ι) :
    initialValueState lambda x 0 = x := by
  simp only [initialValueState, Real.toNNReal_zero, heat_zero, ContinuousLinearMap.id_apply]

theorem initialValueState_norm_le (lambda : ι → NNReal) (x : State ι) (t : ℝ) :
    ‖initialValueState lambda x t‖ ≤ ‖x‖ := norm_heat_apply_le lambda _ x

theorem initialValueState_coeff (lambda : ι → NNReal) (x : State ι)
    {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    initialValueState lambda x t i = Real.exp (-t * lambda i) * x i := by
  rw [initialValueState, heat_apply, Real.coe_toNNReal t ht]

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
