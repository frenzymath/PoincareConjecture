import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CenteredSpectralResidual
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialSpectralDerivative









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63.CenteredSpectralResidual

open SpectralHeatNative

variable {iota : Type*} [Countable iota]
  [MeasurableSpace (State iota)] [BorelSpace (State iota)]
  {lambda : iota → NNReal} {w : State iota} {T r : ℝ}
  (N : CenteredSpectralResidual lambda w T)





theorem exists_initial_spectral_response (hT : 0 ≤ T) (hT1 : T ≤ 1) (hr : 0 ≤ r)
    (hsmall : 2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.principalConstant *
        ‖(initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)‖ +
      2 * N.lowerConstant * Real.sqrt T < 1)
    (hzero : ‖N.zero_memLp.toLp (fun t => N.toFun t 0)‖ ≤
      (1 - (2 * N.perturbationConstant + 8 * N.principalConstant * r +
        2 * N.principalConstant *
          ‖(initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)‖ +
        2 * N.lowerConstant * Real.sqrt T)) * r) :
    ∃ (F : ForcingSpace iota T) (U D G : ℝ → State iota),
      ‖F‖ ≤ r ∧
      U = (fun t => heat lambda t.toNNReal (shiftedBaseMultiplier lambda w) +
        responseState lambda F t) ∧
      D = (fun t => -initialHeatGenerator lambda w t + derivativeState lambda F t) ∧
      G = (fun t => initialHeatGenerator lambda w t + generatorState lambda F t) ∧
      N.forcingResidual hT F = F ∧
      U 0 = shiftedBaseMultiplier lambda w ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (timeMeasure T) ∧ MemLp G 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + G t = N.toFun t (shiftedHighOperator hT lambda F t)) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i, G t i = (lambda i : ℝ) * U t i) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i,
        (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t) i =
          (1 + (lambda i : ℝ)) * U t i) ∧
      (∫ t, ‖D t‖ ^ 2 ∂timeMeasure T) + (∫ t, ‖G t‖ ^ 2 ∂timeMeasure T) ≤
        2 * ‖w‖ ^ 2 + 2 * r ^ 2 ∧
      Tendsto (fun m : ℕ => (N.forcingResidual hT)^[m] 0) atTop (𝓝 F) := by
  let P := (initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)
  let kappa : NNReal :=
    ⟨2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.principalConstant * ‖P‖ + 2 * N.lowerConstant * Real.sqrt T, by positivity⟩
  have hzeroR : ‖N.forcingResidual hT 0‖ ≤ (1 - (kappa : ℝ)) * r := by
    rw [N.forcingResidual_zero]
    exact hzero
  obtain ⟨F, hF, hfix, hiter, _⟩ := exists_forcing_fixedPoint (N.forcingResidual hT)
    hr (show kappa < 1 from hsmall) hzeroR
    (fun V W hV hW => N.norm_forcingResidual_sub_le hT hT1 hr V W hV hW)
  let U := fun t => heat lambda t.toNNReal (shiftedBaseMultiplier lambda w) +
    responseState lambda F t
  let D := fun t => -initialHeatGenerator lambda w t + derivativeState lambda F t
  let G := fun t => initialHeatGenerator lambda w t + generatorState lambda F t
  obtain ⟨hG0, hG0energy⟩ := initialHeatGenerator_memLp_energy lambda w hT
  have hD1 := memLp_derivativeState_of_memLp hT (Lp.memLp F) lambda
  have hG1 := memLp_generatorState_of_memLp hT (Lp.memLp F) lambda
  have hsource := N.forcingResidual_coe hT F
  rw [hfix] at hsource
  refine ⟨F, U, D, G, hF, rfl, rfl, rfl, hfix, ?_, ?_, hG0.neg.add hD1,
    hG0.add hG1, ?_, ?_, ?_, ?_, ?_, hiter⟩
  · simp [U, responseState_zero, heat_zero]
  · exact ((continuous_heat_apply lambda (shiftedBaseMultiplier lambda w)).comp
      continuous_real_toNNReal).continuousOn.add
        (continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda)
  · filter_upwards [ae_hasDerivAt_initialHeat lambda w hT,
      ae_hasDerivAt_responseState_of_memLp hT (Lp.memLp F) lambda] with t h0 h1
    exact h0.add h1
  · filter_upwards [derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda,
      hsource] with t ht hN
    calc
      _ = derivativeState lambda F t + generatorState lambda F t := by dsimp [D, G]; abel
      _ = F t := ht
      _ = _ := hN
  · filter_upwards [ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda,
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    intro i
    change initialHeatGenerator lambda w t i + generatorState lambda F t i =
      (lambda i : ℝ) * (heat lambda t.toNNReal (shiftedBaseMultiplier lambda w) i +
        responseState lambda F t i)
    rw [initialHeatGenerator_eq lambda w hmem.1, heatGenerator_apply, heat_apply,
      Real.coe_toNNReal t hmem.1.le, ht i]
    ring
  · filter_upwards [shiftedHighOperator_coeff hT lambda F,
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    intro i
    change initialHeatHigh lambda w t i + shiftedHighOperator hT lambda F t i =
      (1 + (lambda i : ℝ)) *
        (heat lambda t.toNNReal (shiftedBaseMultiplier lambda w) i + responseState lambda F t i)
    rw [initialHeatHigh_coeff lambda w hmem.1, ht i, heat_apply,
      Real.coe_toNNReal t hmem.1.le]
    ring
  · have hsum (u v : ℝ → State iota) (hu : MemLp u 2 (timeMeasure T))
        (hv : MemLp v 2 (timeMeasure T)) :
        (∫ t, ‖u t + v t‖ ^ 2 ∂timeMeasure T) ≤
          2 * (∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) + 2 * (∫ t, ‖v t‖ ^ 2 ∂timeMeasure T) := by
      have hui := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
      have hvi := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
      calc
        _ ≤ ∫ t, 2 * ‖u t‖ ^ 2 + 2 * ‖v t‖ ^ 2 ∂timeMeasure T := by
          apply integral_mono_ae
            ((memLp_two_iff_integrable_sq_norm (hu.add hv).aestronglyMeasurable).mp (hu.add hv))
            ((hui.const_mul 2).add (hvi.const_mul 2))
          exact Eventually.of_forall (fun t => by
            have hn := pow_le_pow_left₀ (norm_nonneg (u t + v t)) (norm_add_le (u t) (v t)) 2
            change ‖u t + v t‖ ^ 2 ≤ 2 * ‖u t‖ ^ 2 + 2 * ‖v t‖ ^ 2
            nlinarith [sq_nonneg (‖u t‖ - ‖v t‖)])
        _ = _ := by
          rw [integral_add (hui.const_mul 2) (hvi.const_mul 2),
            integral_const_mul, integral_const_mul]
    have hDE := hsum (-initialHeatGenerator lambda w) (derivativeState lambda F) hG0.neg hD1
    have hGE := hsum (initialHeatGenerator lambda w) (generatorState lambda F) hG0 hG1
    simp only [Pi.neg_apply, norm_neg] at hDE
    have hRE := integral_response_energy_le_of_memLp hT (Lp.memLp F) lambda
    rw [← forcing_norm_sq] at hRE
    have hFr := (sq_le_sq₀ (norm_nonneg F) hr).mpr hF
    change (∫ t, ‖-initialHeatGenerator lambda w t + derivativeState lambda F t‖ ^ 2
      ∂timeMeasure T) + (∫ t, ‖initialHeatGenerator lambda w t + generatorState lambda F t‖ ^ 2
      ∂timeMeasure T) ≤ _
    nlinarith




theorem forcing_fixedPoint_unique (hT : 0 ≤ T) (hT1 : T ≤ 1) (hr : 0 ≤ r)
    (hsmall : 2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.principalConstant *
        ‖(initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)‖ +
      2 * N.lowerConstant * Real.sqrt T < 1)
    {F G : ForcingSpace iota T} (hF : ‖F‖ ≤ r) (hG : ‖G‖ ≤ r)
    (hfixF : N.forcingResidual hT F = F) (hfixG : N.forcingResidual hT G = G) : F = G := by
  have h := N.norm_forcingResidual_sub_le hT hT1 hr F G hF hG
  rw [hfixF, hfixG] at h
  have hnorm : ‖F - G‖ = 0 := by nlinarith [norm_nonneg (F - G)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end PoincareConjecture.M63.CenteredSpectralResidual
