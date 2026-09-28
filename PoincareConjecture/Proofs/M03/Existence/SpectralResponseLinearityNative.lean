import PoincareConjecture.Proofs.M03.Existence.SpectralL2ResponseNative

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*}

private theorem coordinate_intervalIntegrable_prefix {T t : ℝ}
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (ht : t ∈ Icc (0 : ℝ) T) (i : iota) :
    IntervalIntegrable (fun s => F s i) volume 0 t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hi := (intervalIntegrable_and_sq_of_memLp_two hT (memLp_coordinate hF i)).1
  apply hi.mono_set
  rw [uIcc_of_le ht.1, uIcc_of_le hT]
  exact Icc_subset_Icc le_rfl ht.2

private theorem mode_zero_add {lambda t : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 t) (hg : IntervalIntegrable g volume 0 t) :
    spectralMode lambda 0 (fun s => f s + g s) t =
      spectralMode lambda 0 f t + spectralMode lambda 0 g t := by
  have he : Continuous (fun s : ℝ => Real.exp (lambda * s)) := by fun_prop
  have hF := hf.continuousOn_mul he.continuousOn
  have hG := hg.continuousOn_mul he.continuousOn
  simp only [spectralMode, zero_add, mul_add]
  rw [intervalIntegral.integral_add hF hG]
  ring

private theorem mode_zero_sub {lambda t : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 t) (hg : IntervalIntegrable g volume 0 t) :
    spectralMode lambda 0 (fun s => f s - g s) t =
      spectralMode lambda 0 f t - spectralMode lambda 0 g t := by
  have he : Continuous (fun s : ℝ => Real.exp (lambda * s)) := by fun_prop
  have hF := hf.continuousOn_mul he.continuousOn
  have hG := hg.continuousOn_mul he.continuousOn
  simp only [spectralMode, zero_add, mul_sub]
  rw [intervalIntegral.integral_sub hF hG]
  ring

private theorem mode_zero_smul (lambda a t : ℝ) (f : ℝ → ℝ) :
    spectralMode lambda 0 (fun s => a * f s) t =
      a * spectralMode lambda 0 f t := by
  simp only [spectralMode, zero_add]
  have he : (fun s => Real.exp (lambda * s) * (a * f s)) =
      (fun s => a * (Real.exp (lambda * s) * f s)) := by
    funext s
    ring
  rw [he, intervalIntegral.integral_const_mul]
  ring

theorem responseState_add_of_memLp [Countable iota] {T t : ℝ}
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal)
    (ht : t ∈ Icc (0 : ℝ) T) :
    responseState lambda (F + G) t = responseState lambda F t + responseState lambda G t := by
  apply lp.ext
  funext i
  change responseState lambda (F + G) t i = responseState lambda F t i +
    responseState lambda G t i
  rw [responseState_apply_of_memLp (hF.add hG) lambda ht,
    responseState_apply_of_memLp hF lambda ht, responseState_apply_of_memLp hG lambda ht]
  exact mode_zero_add (coordinate_intervalIntegrable_prefix hF ht i)
    (coordinate_intervalIntegrable_prefix hG ht i)

theorem responseState_sub_of_memLp [Countable iota] {T t : ℝ}
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal)
    (ht : t ∈ Icc (0 : ℝ) T) :
    responseState lambda (F - G) t = responseState lambda F t - responseState lambda G t := by
  apply lp.ext
  funext i
  change responseState lambda (F - G) t i = responseState lambda F t i -
    responseState lambda G t i
  rw [responseState_apply_of_memLp (hF.sub hG) lambda ht,
    responseState_apply_of_memLp hF lambda ht, responseState_apply_of_memLp hG lambda ht]
  exact mode_zero_sub (coordinate_intervalIntegrable_prefix hF ht i)
    (coordinate_intervalIntegrable_prefix hG ht i)

theorem responseState_smul_of_memLp [Countable iota] {T t : ℝ}
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (a : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    responseState lambda (a • F) t = a • responseState lambda F t := by
  apply lp.ext
  funext i
  change responseState lambda (a • F) t i = a * responseState lambda F t i
  rw [responseState_apply_of_memLp (hF.const_smul a) lambda ht,
    responseState_apply_of_memLp hF lambda ht]
  exact mode_zero_smul (lambda i) a t (fun s => F s i)

theorem ae_generatorState_add_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal) :
    generatorState lambda (F + G) =ᵐ[timeMeasure T]
      (fun t => generatorState lambda F t + generatorState lambda G t) := by
  filter_upwards [ae_generatorState_apply_of_memLp hT (hF.add hG) lambda,
    ae_generatorState_apply_of_memLp hT hF lambda,
    ae_generatorState_apply_of_memLp hT hG lambda,
    ae_restrict_mem measurableSet_Ioc] with t hsum hFi hGi hmem
  apply lp.ext
  funext i
  change generatorState lambda (F + G) t i = generatorState lambda F t i +
    generatorState lambda G t i
  rw [hsum i, hFi i, hGi i,
    responseState_add_of_memLp hF hG lambda (Ioc_subset_Icc_self hmem)]
  change (lambda i : ℝ) * (responseState lambda F t i + responseState lambda G t i) = _
  ring

theorem ae_generatorState_sub_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal) :
    generatorState lambda (F - G) =ᵐ[timeMeasure T]
      (fun t => generatorState lambda F t - generatorState lambda G t) := by
  filter_upwards [ae_generatorState_apply_of_memLp hT (hF.sub hG) lambda,
    ae_generatorState_apply_of_memLp hT hF lambda,
    ae_generatorState_apply_of_memLp hT hG lambda,
    ae_restrict_mem measurableSet_Ioc] with t hsub hFi hGi hmem
  apply lp.ext
  funext i
  change generatorState lambda (F - G) t i = generatorState lambda F t i -
    generatorState lambda G t i
  rw [hsub i, hFi i, hGi i,
    responseState_sub_of_memLp hF hG lambda (Ioc_subset_Icc_self hmem)]
  change (lambda i : ℝ) * (responseState lambda F t i - responseState lambda G t i) = _
  ring

theorem ae_generatorState_smul_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (a : ℝ) :
    generatorState lambda (a • F) =ᵐ[timeMeasure T]
      (fun t => a • generatorState lambda F t) := by
  filter_upwards [ae_generatorState_apply_of_memLp hT (hF.const_smul a) lambda,
    ae_generatorState_apply_of_memLp hT hF lambda,
    ae_restrict_mem measurableSet_Ioc] with t hsmul hFi hmem
  apply lp.ext
  funext i
  change generatorState lambda (a • F) t i = a * generatorState lambda F t i
  rw [hsmul i, hFi i, responseState_smul_of_memLp hF lambda a (Ioc_subset_Icc_self hmem)]
  change (lambda i : ℝ) * (a * responseState lambda F t i) = _
  ring

theorem ae_derivativeState_add_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal) :
    derivativeState lambda (F + G) =ᵐ[timeMeasure T]
      (fun t => derivativeState lambda F t + derivativeState lambda G t) := by
  filter_upwards [derivativeState_add_generatorState_of_memLp hT (hF.add hG) lambda,
    derivativeState_add_generatorState_of_memLp hT hF lambda,
    derivativeState_add_generatorState_of_memLp hT hG lambda,
    ae_generatorState_add_of_memLp hT hF hG lambda] with t hsum hFi hGi hgen
  rw [eq_sub_iff_add_eq.mpr hsum, eq_sub_iff_add_eq.mpr hFi,
    eq_sub_iff_add_eq.mpr hGi, hgen]
  simp only [Pi.add_apply]
  abel

theorem ae_derivativeState_sub_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal) :
    derivativeState lambda (F - G) =ᵐ[timeMeasure T]
      (fun t => derivativeState lambda F t - derivativeState lambda G t) := by
  filter_upwards [derivativeState_add_generatorState_of_memLp hT (hF.sub hG) lambda,
    derivativeState_add_generatorState_of_memLp hT hF lambda,
    derivativeState_add_generatorState_of_memLp hT hG lambda,
    ae_generatorState_sub_of_memLp hT hF hG lambda] with t hsub hFi hGi hgen
  rw [eq_sub_iff_add_eq.mpr hsub, eq_sub_iff_add_eq.mpr hFi,
    eq_sub_iff_add_eq.mpr hGi, hgen]
  simp only [Pi.sub_apply]
  abel

theorem ae_derivativeState_smul_of_memLp [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (lambda : iota → NNReal) (a : ℝ) :
    derivativeState lambda (a • F) =ᵐ[timeMeasure T]
      (fun t => a • derivativeState lambda F t) := by
  filter_upwards [derivativeState_add_generatorState_of_memLp hT (hF.const_smul a) lambda,
    derivativeState_add_generatorState_of_memLp hT hF lambda,
    ae_generatorState_smul_of_memLp hT hF lambda a] with t hsmul hFi hgen
  rw [eq_sub_iff_add_eq.mpr hsmul, eq_sub_iff_add_eq.mpr hFi, hgen]
  simp only [Pi.smul_apply, smul_sub]

theorem responseState_eq_of_ae_eq [Countable iota] {T t : ℝ}
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal)
    (hFG : F =ᵐ[timeMeasure T] G) (ht : t ∈ Icc (0 : ℝ) T) :
    responseState lambda F t = responseState lambda G t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  apply lp.ext
  funext i
  rw [responseState_apply_of_memLp hF lambda ht, responseState_apply_of_memLp hG lambda ht]
  change spectralMode (lambda i) 0 (fun s => F s i) t =
    spectralMode (lambda i) 0 (fun s => G s i) t
  apply spectralMode_eq_of_ae_eq (T := T) (f := fun s => F s i) (g := fun s => G s i)
  · rw [uIoc_of_le hT]
    change ∀ᵐ s ∂timeMeasure T, F s i = G s i
    exact hFG.mono (fun s hs => congrArg (fun v : State iota => v i) hs)
  · simpa only [uIcc_of_le hT] using ht

theorem ae_generatorState_eq_of_ae_eq [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal)
    (hFG : F =ᵐ[timeMeasure T] G) :
    generatorState lambda F =ᵐ[timeMeasure T] generatorState lambda G := by
  filter_upwards [ae_generatorState_apply_of_memLp hT hF lambda,
    ae_generatorState_apply_of_memLp hT hG lambda,
    ae_restrict_mem measurableSet_Ioc] with t hFi hGi hmem
  apply lp.ext
  funext i
  rw [hFi i, hGi i, responseState_eq_of_ae_eq hF hG lambda hFG (Ioc_subset_Icc_self hmem)]

theorem ae_derivativeState_eq_of_ae_eq [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal)
    (hFG : F =ᵐ[timeMeasure T] G) :
    derivativeState lambda F =ᵐ[timeMeasure T] derivativeState lambda G := by
  filter_upwards [derivativeState_add_generatorState_of_memLp hT hF lambda,
    derivativeState_add_generatorState_of_memLp hT hG lambda,
    ae_generatorState_eq_of_ae_eq hT hF hG lambda hFG, hFG] with t hFi hGi hgen hfg
  rw [eq_sub_iff_add_eq.mpr hFi, eq_sub_iff_add_eq.mpr hGi, hgen, hfg]

theorem integral_response_difference_energy_le [Countable iota] {T : ℝ} (hT : 0 ≤ T)
    {F G : ℝ → State iota} (hF : MemLp F 2 (timeMeasure T))
    (hG : MemLp G 2 (timeMeasure T)) (lambda : iota → NNReal) :
    (∫ t, ‖derivativeState lambda F t - derivativeState lambda G t‖ ^ 2 ∂timeMeasure T) +
        (∫ t, ‖generatorState lambda F t - generatorState lambda G t‖ ^ 2 ∂timeMeasure T) ≤
      ∫ t, ‖F t - G t‖ ^ 2 ∂timeMeasure T := by
  have he := integral_response_energy_le_of_memLp hT (hF.sub hG) lambda
  have hD : (∫ t, ‖derivativeState lambda (F - G) t‖ ^ 2 ∂timeMeasure T) =
      ∫ t, ‖derivativeState lambda F t - derivativeState lambda G t‖ ^ 2 ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_derivativeState_sub_of_memLp hT hF hG lambda] with t ht
    rw [ht]
  have hA : (∫ t, ‖generatorState lambda (F - G) t‖ ^ 2 ∂timeMeasure T) =
      ∫ t, ‖generatorState lambda F t - generatorState lambda G t‖ ^ 2 ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_generatorState_sub_of_memLp hT hF hG lambda] with t ht
    rw [ht]
  rw [hD, hA] at he
  exact he

end PoincareConjecture.SpectralHeatNative
