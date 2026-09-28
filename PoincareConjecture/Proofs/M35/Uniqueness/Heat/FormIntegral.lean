import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormPrimitive
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.NonautonomousFormHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem formWeakHeat_integral_value_trace (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : Lp V 2 (timeMeasure T)) :
    ∃ U : ℝ → H, U 0 = 0 ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (formWeakHeatOperator J hc hd hi hn hT F t) = U t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U t) =
        ∫ s in (0 : ℝ)..t, F s - formWeakHeatOperator J hc hd hi hn hT F s +
          J.adjoint (J (formWeakHeatOperator J hc hd hi hn hT F s)) := by
  let B := (formEigenbasis J hc hd hi).repr
  let C := B.toContinuousLinearEquiv.toContinuousLinearMap
  let E := C.compLpL 2 (timeMeasure T) F
  obtain ⟨U, hU0, hUc, hUv, _⟩ := formWeakHeat_value_trace J hc hd hi hn hT F
  have hUP : ∀ t ∈ Icc 0 T, J.adjoint (U t) =
      formDualPrimitive J hc hd hi hn E t := by
    apply adjoint_value_trace_eq J hU0 (formDualPrimitive_zero J hc hd hi hn E) hUc
      (continuousOn_formDualPrimitive J hc hd hi hn hT E)
    filter_upwards [hUv, formDualPrimitive_graph J hc hd hi hn hT E] with t hu hp
    rw [← hu]
    exact hp
  refine ⟨U, hU0, hUc, hUv, ?_⟩
  intro t ht
  rw [hUP t ht, formDualPrimitive_integral J hc hd hi hn hT E ht]
  apply intervalIntegral.integral_congr_ae_restrict
  have he : ∀ᵐ s ∂timeMeasure T, B.symm (E s) = F s := by
    filter_upwards [C.coeFn_compLpL F] with s hs
    rw [hs]
    exact B.symm_apply_apply (F s)
  have het := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) he
  rw [uIoc_of_le ht.1]
  filter_upwards [het] with s hs
  rw [hs]
  rfl

end PoincareConjecture.M35.Uniqueness.Heat
