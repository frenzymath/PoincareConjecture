import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormPerturbedHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormValueForcingNorm










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem norm_mixed_form_response_le (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (R : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (L : Lp V 2 (timeMeasure T) →L[ℝ] Lp H 2 (timeMeasure T)) :
    ‖(formWeakHeatOperator J hc hd hi hn hT).comp
      (R + (J.adjoint.compLpL 2 (timeMeasure T)).comp L)‖ ≤
        (T + 1) * ‖R‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖L‖ := by
  rw [ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_assoc]
  change ‖(formWeakHeatOperator J hc hd hi hn hT).comp R +
    (formValueHeatOperator J hc hd hi hn hT).comp L‖ ≤ _
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_formWeakHeatOperator_le J hc hd hi hn hT)
        (norm_nonneg R))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_formValueHeatOperator_le J hc hd hi hn hT)
        (norm_nonneg L))



theorem exists_mixed_perturbed_form_heat (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (R : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (L : Lp V 2 (timeMeasure T) →L[ℝ] Lp H 2 (timeMeasure T))
    (hsmall : (T + 1) * ‖R‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖L‖ < 1)
    (F : Lp V 2 (timeMeasure T)) :
    let M := R + (J.adjoint.compLpL 2 (timeMeasure T)).comp L
    ∃ (v : Lp V 2 (timeMeasure T)) (P D : ℝ → V),
      P 0 = 0 ∧ ContinuousOn P (Icc (0 : ℝ) T) ∧ MemLp D 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt P (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, J.adjoint (J (v t)) = P t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + v t - P t = (M v + F) t) ∧
      formWeakHeatOperator J hc hd hi hn hT (M v + F) = v :=
  exists_form_heat_of_contractive_response J hc hd hi hn hT _
    ((norm_mixed_form_response_le J hc hd hi hn hT R L).trans_lt hsmall) F

end PoincareConjecture.M35.Uniqueness.Heat
