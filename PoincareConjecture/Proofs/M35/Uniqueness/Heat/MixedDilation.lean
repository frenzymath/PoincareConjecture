import PoincareConjecture.Proofs.M35.Uniqueness.Heat.NormalizedDilation
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDependentOperator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormMixedHeat









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

omit [SeparableSpace H] in
theorem normalizedDilationLp_one_eq_mixed
    (J : V →L[ℝ] H) {a b T B q C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (h1 : (1 : ℝ) ∈ Icc a b)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B))
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ q)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (hgen : ∀ t ∈ Icc 0 T, A t = R t + J.adjoint.comp (L t) -
      ContinuousLinearMap.id ℝ V + J.adjoint.comp J) :
    normalizedDilationLp J ha hab hT hBT hB A hA 1 =
      timeDependentLpOperator hRm hRb +
        (J.adjoint.compLpL 2 (timeMeasure T)).comp (timeDependentLpOperator hLm hLb) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  let Ru := timeDependentLpOperator hRm hRb u
  let Lu := timeDependentLpOperator hLm hLb u
  filter_upwards [normalizedDilationLp_generator J ha hab hT hBT hB A hA h1 u,
    timeDependentLpOperator_coe hRm hRb u, timeDependentLpOperator_coe hLm hLb u,
    J.adjoint.coeFn_compLpL (p := 2) (μ := timeMeasure T) Lu,
    Lp.coeFn_add Ru (J.adjoint.compLpL 2 (timeMeasure T) Lu),
    ae_restrict_mem measurableSet_Ioc] with t hg hr hl hj hs ht
  rw [one_smul, one_mul, hgen t (Ioc_subset_Icc_self ht)] at hg
  change _ = (Ru + J.adjoint.compLpL 2 (timeMeasure T) Lu) t
  rw [hs, Pi.add_apply, hj]
  change _ = Ru t + J.adjoint (Lu t)
  rw [hr, hl]
  change _ - u t + J.adjoint (J (u t)) =
    R t (u t) + J.adjoint (L t (u t)) - u t + J.adjoint (J (u t)) at hg
  exact sub_left_injective (add_right_cancel hg)

theorem norm_normalizedDilationLp_response_lt_one
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {a b T B q C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (h1 : (1 : ℝ) ∈ Icc a b) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B))
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ q)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (hgen : ∀ t ∈ Icc 0 T, A t = R t + J.adjoint.comp (L t) -
      ContinuousLinearMap.id ℝ V + J.adjoint.comp J)
    (hsmall : (T + 1) * q + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1) :
    ‖(formWeakHeatOperator J hc hd hi hn hT).comp
      (normalizedDilationLp J ha hab hT hBT hB A hA 1)‖ < 1 := by
  rw [normalizedDilationLp_one_eq_mixed J ha hab hT hBT hB h1 A hA R hRm hRb L hLm hLb hgen]
  apply (norm_mixed_form_response_le J hc hd hi hn hT _ _).trans_lt
  apply lt_of_le_of_lt _ hsmall
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hRm hRb hq)
      (by positivity)
  · exact mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hLm hLb hC)
      (by positivity)

end PoincareConjecture.M35.Uniqueness.Heat
