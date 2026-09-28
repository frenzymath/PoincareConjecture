import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TimeDependentSpectralResidual











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63.TimeDependentSpectralResidual

open SpectralHeatNative

variable {iota : Type*} [Countable iota]
  [MeasurableSpace (State iota)] [BorelSpace (State iota)]
  {lambda : iota → NNReal} {T r : ℝ}
  (N : TimeDependentSpectralResidual lambda T)






theorem exists_spectral_response (hT : 0 ≤ T) (hT1 : T ≤ 1) (hr : 0 ≤ r)
    (hsmall : 2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.lowerConstant * Real.sqrt T < 1)
    (hzero : ‖N.zero_memLp.toLp (fun t => N.toFun t 0)‖ ≤
      (1 - (2 * N.perturbationConstant + 8 * N.principalConstant * r +
        2 * N.lowerConstant * Real.sqrt T)) * r) :
    ∃ (F : ForcingSpace iota T) (U D G : ℝ → State iota),
      ‖F‖ ≤ r ∧ U = responseState lambda F ∧ N.forcingResidual hT F = F ∧
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (timeMeasure T) ∧ MemLp G 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T,
        D t + G t = N.toFun t (shiftedHighOperator hT lambda F t)) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i, G t i = (lambda i : ℝ) * U t i) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i,
        shiftedHighOperator hT lambda F t i = (1 + (lambda i : ℝ)) * U t i) ∧
      (∫ t, ‖D t‖ ^ 2 ∂timeMeasure T) + (∫ t, ‖G t‖ ^ 2 ∂timeMeasure T) ≤ r ^ 2 ∧
      Tendsto (fun m : ℕ => (N.forcingResidual hT)^[m] 0) atTop (𝓝 F) := by
  let kappa : NNReal :=
    ⟨2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.lowerConstant * Real.sqrt T, by positivity⟩
  have hzeroR : ‖N.forcingResidual hT 0‖ ≤ (1 - (kappa : ℝ)) * r := by
    rw [N.forcingResidual_zero]
    exact hzero
  obtain ⟨F, hF, hfix, hiter, _⟩ := exists_forcing_fixedPoint (N.forcingResidual hT)
    hr (show kappa < 1 from hsmall) hzeroR
    (fun V W hV hW => N.norm_forcingResidual_sub_le hT hT1 hr V W hV hW)
  have hsource := N.forcingResidual_coe hT F
  rw [hfix] at hsource
  refine ⟨F, responseState lambda F, derivativeState lambda F, generatorState lambda F,
    hF, rfl, hfix, responseState_zero lambda F,
    continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda,
    memLp_derivativeState_of_memLp hT (Lp.memLp F) lambda,
    memLp_generatorState_of_memLp hT (Lp.memLp F) lambda,
    ae_hasDerivAt_responseState_of_memLp hT (Lp.memLp F) lambda, ?_,
    ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda,
    shiftedHighOperator_coeff hT lambda F, ?_, hiter⟩
  · filter_upwards [derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda,
      hsource] with t ht hN
    exact ht.trans hN
  · calc
      _ ≤ ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T :=
        integral_response_energy_le_of_memLp hT (Lp.memLp F) lambda
      _ = ‖F‖ ^ 2 := (forcing_norm_sq F).symm
      _ ≤ r ^ 2 := (sq_le_sq₀ (norm_nonneg F) hr).mpr hF





theorem forcing_fixedPoint_unique (hT : 0 ≤ T) (hT1 : T ≤ 1) (hr : 0 ≤ r)
    (hsmall : 2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.lowerConstant * Real.sqrt T < 1)
    {F G : ForcingSpace iota T} (hF : ‖F‖ ≤ r) (hG : ‖G‖ ≤ r)
    (hfixF : N.forcingResidual hT F = F) (hfixG : N.forcingResidual hT G = G) : F = G := by
  have h := N.norm_forcingResidual_sub_le hT hT1 hr F G hF hG
  rw [hfixF, hfixG] at h
  have hnorm : ‖F - G‖ = 0 := by nlinarith [norm_nonneg (F - G)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end PoincareConjecture.M63.TimeDependentSpectralResidual
