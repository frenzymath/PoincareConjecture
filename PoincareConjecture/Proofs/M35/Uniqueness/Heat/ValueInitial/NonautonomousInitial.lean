import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.MixedInitial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem exists_nonautonomous_value_initial_integral_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * A + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (F : Lp V 2 (timeMeasure T)) (u₀ : H) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint u₀ +
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
    exists_mixed_value_initial_integral_heat J hc hd hi hn hT RR LL hsmall' F u₀
  refine ⟨v, U, hU0, hUc, hUv, ?_⟩
  intro t ht
  rw [hUi t ht]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl ht.2) (timeDependentLpOperator_coe hRm hRb v),
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
      (timeDependentLpOperator_coe hLm hLb v)] with s hr hl
  rw [hr, hl]

theorem exists_nonautonomous_value_initial_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * A + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (F : Lp V 2 (timeMeasure T)) (u₀ : H) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ w : V,
        HasDerivWithinAt (fun s => inner ℝ (J w) (U s))
          (inner ℝ w (R t (v t) + F t) + inner ℝ (J w) (L t (v t)) -
            (inner ℝ w (v t) - inner ℝ (J w) (J (v t)))) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint u₀ +
        ∫ s in (0 : ℝ)..t, R s (v s) + J.adjoint (L s (v s)) + F s - v s +
          J.adjoint (J (v s))) := by
  obtain ⟨v, U, hU0, hUc, hUv, hUi⟩ :=
    exists_nonautonomous_value_initial_integral_heat
      J hc hd hi hn hT hA hC R hRm hRb L hLm hLb hsmall F u₀
  let D : ℝ → V := fun s => R s (v s) + J.adjoint (L s (v s)) + F s - v s +
    J.adjoint (J (v s))
  have hD : MemLp D 2 (timeMeasure T) :=
    ((((memLp_timeDependent_apply hRm hRb v).add
      (J.adjoint.comp_memLp' (memLp_timeDependent_apply hLm hLb v))).add
      (Lp.memLp F)).sub (Lp.memLp v)).add
      (J.adjoint.comp_memLp' (J.comp_memLp' (Lp.memLp v)))
  have hDi : IntervalIntegrable D volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (hD.integrable (by norm_num))
  refine ⟨v, U, hU0, hUc, hUv, ?_, hUi⟩
  filter_upwards [ae_restrict_of_ae hDi.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioc] with t ht htime
  have ht' : t ∈ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    exact Ioc_subset_Icc_self htime
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) T := by simp [hT]
  have hdU : HasDerivAt (fun s => J.adjoint u₀ + ∫ z in (0 : ℝ)..s, D z)
      (D t) t := (ht ht' 0 h0).const_add _
  intro w
  have hp : ∀ s ∈ Icc (0 : ℝ) T, inner ℝ (J w) (U s) =
      inner ℝ w (J.adjoint u₀ + ∫ z in (0 : ℝ)..s, D z) := by
    intro s hs
    rw [← hUi s hs, J.adjoint_inner_right]
  have hw : HasDerivWithinAt (fun s => inner ℝ (J w) (U s))
      (inner ℝ w (D t)) (Icc 0 T) t :=
    (((innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t hdU).hasDerivWithinAt).congr_of_mem
      hp (Ioc_subset_Icc_self htime)
  apply hw.congr_deriv
  simp only [D, inner_add_right, inner_sub_right, J.adjoint_inner_right]
  ring

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
