import PoincareConjecture.Proofs.M03.Existence.SpectralResponseNative
import PoincareConjecture.Proofs.M03.Existence.SpectralModeStateNative

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralTraceNative

open SpectralHeatNative

variable {iota : Type*}

def coordinateEnergy (T : ℝ) (F : ℝ → State iota) (i : iota) : ℝ :=
  ∫ t, F t i ^ 2 ∂timeMeasure T

theorem coordinateEnergy_nonneg (T : ℝ) (F : ℝ → State iota) (i : iota) :
    0 ≤ coordinateEnergy T F i := integral_nonneg (fun _ => sq_nonneg _)

theorem coordinate_memLp {T : ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (i : iota) :
    MemLp (fun t => F t i) 2 (timeMeasure T) :=
  hF.continuousLinearMap_comp (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i)

theorem tsum_ofReal_coordinateEnergy [Countable iota] {T : ℝ}
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T)) :
    (∑' i, ENNReal.ofReal (coordinateEnergy T F i)) =
      ∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂timeMeasure T := by
  calc
    _ = ∑' i, ∫⁻ t, ENNReal.ofReal (F t i ^ 2) ∂timeMeasure T := by
      apply tsum_congr
      intro i
      exact ofReal_integral_eq_lintegral_ofReal (coordinate_memLp hF i).integrable_sq
        (Eventually.of_forall (fun _ => sq_nonneg _))
    _ = ∫⁻ t, squareSum (F t) ∂timeMeasure T := by
      exact (lintegral_tsum (fun i =>
        ((coordinate_memLp hF i).1.aemeasurable.pow_const 2).ennreal_ofReal)).symm
    _ = _ := by simp only [squareSum_state]

theorem coordinateEnergy_summable [Countable iota] {T : ℝ}
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T)) :
    Summable (coordinateEnergy T F) := by
  have hi := (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have hne : (∑' i, ENNReal.ofReal (coordinateEnergy T F i)) ≠ ∞ := by
    rw [tsum_ofReal_coordinateEnergy hF,
      ← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_ne_top
  have hs := ENNReal.summable_toReal hne
  simpa only [ENNReal.toReal_ofReal (coordinateEnergy_nonneg T F _)] using hs

theorem tsum_coordinateEnergy [Countable iota] {T : ℝ}
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T)) :
    (∑' i, coordinateEnergy T F i) = ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  have hi := (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have he := tsum_ofReal_coordinateEnergy hF
  rw [← ENNReal.ofReal_tsum_of_nonneg (coordinateEnergy_nonneg T F)
    (coordinateEnergy_summable hF),
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun _ => sq_nonneg _))] at he
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg (coordinateEnergy_nonneg T F)),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))] using
    congrArg ENNReal.toReal he

def traceCoeff (lambda : iota → NNReal) (F : ℝ → State iota) (t : ℝ) (i : iota) : ℝ :=
  Real.sqrt (lambda i) * responseCoeff lambda F t i

theorem traceCoeff_sq_le {T t : ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (lambda : iota → NNReal)
    (ht : t ∈ Icc (0 : ℝ) T) (i : iota) :
    traceCoeff lambda F t i ^ 2 ≤ coordinateEnergy T F i := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hFi := coordinate_memLp hF i
  have hprefix : (lambda i : ℝ) * responseCoeff lambda F t i ^ 2 ≤
      ∫ s in (0 : ℝ)..t, F s i ^ 2 := by
    simpa only [responseCoeff, zero_pow two_ne_zero, mul_zero, add_zero] using
      spectralMode_trace_energy_le_of_memLp (c := 0) (lambda i).coe_nonneg hFi ht
  have hmono := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Eventually.of_forall (fun s => sq_nonneg (F s i)))
    (intervalIntegrable_and_sq_of_memLp_two hT hFi).2
  rw [traceCoeff, mul_pow, Real.sq_sqrt (lambda i).coe_nonneg]
  exact hprefix.trans (by simpa only [coordinateEnergy, intervalIntegral.integral_of_le hT]
    using hmono)

theorem traceCoeff_memℓp [Countable iota] {T t : ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (lambda : iota → NNReal)
    (ht : t ∈ Icc (0 : ℝ) T) : Memℓp (traceCoeff lambda F t) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  have hs := (coordinateEnergy_summable hF).of_nonneg_of_le
    (fun i => sq_nonneg (traceCoeff lambda F t i)) (traceCoeff_sq_le hF lambda ht)
  simpa using hs

def traceState (lambda : iota → NNReal) (F : ℝ → State iota) (t : ℝ) : State iota :=
  stateOfCoeffs (traceCoeff lambda F t)

theorem traceState_apply [Countable iota] {T t : ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (lambda : iota → NNReal)
    (ht : t ∈ Icc (0 : ℝ) T) (i : iota) :
    traceState lambda F t i = traceCoeff lambda F t i :=
  stateOfCoeffs_apply (traceCoeff_memℓp hF lambda ht) i

theorem norm_traceState_sq_le [Countable iota] {T t : ℝ} {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (lambda : iota → NNReal)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖traceState lambda F t‖ ^ 2 ≤ ∫ s, ‖F s‖ ^ 2 ∂timeMeasure T := by
  rw [norm_sq_eq_tsum, ← tsum_coordinateEnergy hF]
  apply Summable.tsum_le_tsum
  · intro i
    simpa only [traceState_apply hF lambda ht, sq_abs] using traceCoeff_sq_le hF lambda ht i
  · simpa using (lp.memℓp (traceState lambda F t)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  · exact coordinateEnergy_summable hF

theorem continuousOn_traceCoeff {T : ℝ} (hT : 0 ≤ T) {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (lambda : iota → NNReal) (i : iota) :
    ContinuousOn (fun t => traceCoeff lambda F t i) (Icc (0 : ℝ) T) := by
  have hc := (absolutelyContinuousOnInterval_spectralMode
    (lambda := (lambda i : ℝ)) (c := 0)
    (intervalIntegrable_and_sq_of_memLp_two hT (coordinate_memLp hF i)).1).continuousOn
  have hmode : ContinuousOn (fun t => responseCoeff lambda F t i) (Icc (0 : ℝ) T) := by
    simpa only [responseCoeff, uIcc_of_le hT] using hc
  exact continuousOn_const.mul hmode

theorem continuousOn_traceState [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) :
    ContinuousOn (traceState lambda F) (Icc (0 : ℝ) T) := by
  have hc (i : iota) : ContinuousOn (fun t => traceState lambda F t i) (Icc (0 : ℝ) T) :=
    (continuousOn_traceCoeff hT hF lambda i).congr
      (fun t ht => traceState_apply hF lambda ht i)
  intro t ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsum := (coordinateEnergy_summable hF).mul_left 4
  have hconv : Tendsto
      (fun s => ∑' i, |traceState lambda F s i - traceState lambda F t i| ^ 2)
      (𝓝[Icc (0 : ℝ) T] t) (𝓝 (∑' _i : iota, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro i
      have hct : Tendsto (fun s => traceState lambda F s i)
          (𝓝[Icc (0 : ℝ) T] t) (𝓝 (traceState lambda F t i)) := hc i t ht
      simpa using (hct.sub (tendsto_const_nhds (x := traceState lambda F t i))).pow 2
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro i
      have hsbound := traceCoeff_sq_le hF lambda hs i
      have htbound := traceCoeff_sq_le hF lambda ht i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs,
        traceState_apply hF lambda hs, traceState_apply hF lambda ht]
      nlinarith [sq_nonneg (traceCoeff lambda F s i + traceCoeff lambda F t i)]
  have hn : ∀ s : ℝ,
      ‖traceState lambda F s - traceState lambda F t‖ ^ 2 =
        ∑' i, |traceState lambda F s i - traceState lambda F t i| ^ 2 := by
    intro s
    rw [norm_sq_eq_tsum]
    rfl
  simp only [tsum_zero] at hconv
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, ← hn, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

theorem traceState_zero [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) : traceState lambda F 0 = 0 := by
  apply lp.ext
  funext i
  rw [traceState_apply hF lambda ⟨le_rfl, hT⟩]
  simp [traceCoeff, responseCoeff]

end PoincareConjecture.SpectralTraceNative
