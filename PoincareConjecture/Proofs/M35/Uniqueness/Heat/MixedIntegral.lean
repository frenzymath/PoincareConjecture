import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormIntegral
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormMixedHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem exists_mixed_integral_heat (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (R : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (L : Lp V 2 (timeMeasure T) →L[ℝ] Lp H 2 (timeMeasure T))
    (hsmall : (T + 1) * ‖R‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖L‖ < 1)
    (F : Lp V 2 (timeMeasure T)) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = 0 ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U t) =
        ∫ s in (0 : ℝ)..t, (R v) s + J.adjoint ((L v) s) + F s - v s +
          J.adjoint (J (v s)) := by
  let M := R + (J.adjoint.compLpL 2 (timeMeasure T)).comp L
  obtain ⟨v, _, _, _, _, _, _, _, _, hv⟩ :=
    exists_mixed_perturbed_form_heat J hc hd hi hn hT R L hsmall F
  obtain ⟨U, hU0, hUc, hUv, hUi⟩ :=
    formWeakHeat_integral_value_trace J hc hd hi hn hT (M v + F)
  rw [hv] at hUv hUi
  refine ⟨v, U, hU0, hUc, hUv, ?_⟩
  intro t ht
  rw [hUi t ht]
  apply intervalIntegral.integral_congr_ae_restrict
  have hMcoe : ∀ᵐ s ∂timeMeasure T,
      (M v + F) s = (R v) s + J.adjoint ((L v) s) + F s := by
    have hM : M v = R v + J.adjoint.compLpL 2 (timeMeasure T) (L v) := rfl
    rw [hM]
    filter_upwards [Lp.coeFn_add (R v + J.adjoint.compLpL 2 (timeMeasure T) (L v)) F,
      Lp.coeFn_add (R v) (J.adjoint.compLpL 2 (timeMeasure T) (L v)),
      J.adjoint.coeFn_compLpL (L v)] with s hs hs' hj
    rw [hs, Pi.add_apply, hs', Pi.add_apply, hj]
  rw [uIoc_of_le ht.1]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl ht.2) hMcoe] with s hs
  rw [hs]

theorem exists_nonautonomous_mixed_integral_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * A + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (F : Lp V 2 (timeMeasure T)) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = 0 ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U t) =
        ∫ s in (0 : ℝ)..t, R s (v s) + J.adjoint (L s (v s)) + F s - v s +
          J.adjoint (J (v s)) := by
  let RR := timeDependentLpOperator hRm hRb
  let LL := timeDependentLpOperator hLm hLb
  have hsmall' : (T + 1) * ‖RR‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖LL‖ < 1 :=
    (add_le_add
      (mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hRm hRb hA) (by positivity))
      (mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hLm hLb hC)
        (by positivity))).trans_lt hsmall
  obtain ⟨v, U, hU0, hUc, hUv, hUi⟩ :=
    exists_mixed_integral_heat J hc hd hi hn hT RR LL hsmall' F
  refine ⟨v, U, hU0, hUc, hUv, ?_⟩
  intro t ht
  rw [hUi t ht]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl ht.2) (timeDependentLpOperator_coe hRm hRb v),
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
      (timeDependentLpOperator_coe hLm hLb v)] with s hr hl
  rw [hr, hl]

end PoincareConjecture.M35.Uniqueness.Heat
