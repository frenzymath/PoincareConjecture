import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TwiceRecovery
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.StrongMixedInitial










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

theorem exists_second_compatible_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C D E : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (K₁ K₂ : ℝ → V →L[ℝ] V)
    (hK : ContDiffOn ℝ 1 (fun t => mixedHeatOperator J (R t) (L t)) (Icc 0 T))
    (hK₁ : ContDiffOn ℝ 1 K₁ (Icc 0 T)) (hK₂ : ContinuousOn K₂ (Icc 0 T))
    (hKd : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => mixedHeatOperator J (R s) (L s)) (K₁ t) t)
    (hK₁d : ∀ t ∈ Ioo 0 T, HasDerivAt K₁ (K₂ t) t)
    (hDb : ∀ᵐ t ∂timeMeasure T, ‖-K₁ t - K₁ t‖ ≤ D)
    (hEb : ∀ᵐ t ∂timeMeasure T, ‖-K₂ t‖ ≤ E)
    (hsmall : (T + 1) * (A + D * T + E * (T * T)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (u₀ w₀ z₀ : V)
    (hcompat : J.adjoint (J w₀) + mixedHeatOperator J (R 0) (L 0) u₀ = 0)
    (hcompat₁ : J.adjoint (J z₀) + mixedHeatOperator J (R 0) (L 0) w₀ + K₁ 0 u₀ = 0) :
    ∃ (u w : ℝ → V) (Z : ℝ → H), u 0 = u₀ ∧ w 0 = w₀ ∧ Z 0 = J z₀ ∧
      ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧ ContinuousOn Z (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => J (w s)) (Z t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, J.adjoint (J (w t)) +
        mixedHeatOperator J (R t) (L t) (u t) = 0) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (Z t) +
        mixedHeatOperator J (R t) (L t) (w t) + K₁ t (u t) = 0 := by
  let K := fun t => mixedHeatOperator J (R t) (L t)
  let B := fun t => -K₁ t - K₁ t
  let N := fun t => -K₂ t
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] V) := ⟨Or.inl inferInstance⟩
  have hBm : AEStronglyMeasurable B (timeMeasure T) :=
    (((hK₁.continuousOn.neg).sub hK₁.continuousOn).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hNm : AEStronglyMeasurable N (timeMeasure T) :=
    ((hK₂.neg).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  obtain ⟨u, w, z, Z, hz, hu0, hw0, hZ0, hu, hw, hZ, hgraph, hwi, hui, hdu, _, hZi⟩ :=
    exists_twice_differentiated_form_heat J hc hd hi hn hT hA hC hD hE
      R hRm hRb L hLm hLb B hBm hDb N hNm hEb hsmall u₀ w₀ z₀
  have hZi' (t : ℝ) (ht : t ∈ Icc 0 T) : J.adjoint (Z t) = J.adjoint (J z₀) +
      ∫ s in (0 : ℝ)..t, -K s (z s) - K₁ s (w s) - K₁ s (w s) - K₂ s (u s) := by
    rw [hZi t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only [K, B, N, mixedHeatOperator, sub_apply, neg_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
    abel
  have hrec := twice_heat_recovery J hT K K₁ K₂ hK hK₁ hK₂ hKd hK₁d
    u w z Z u₀ w₀ z₀ hz hu hw hZ hgraph hwi hui hZi' hcompat hcompat₁
  exact ⟨u, w, Z, hu0, hw0, hZ0, hu, hw, hZ, hdu, hrec.2.2, hrec.1, hrec.2.1⟩

end PoincareConjecture.M35.Uniqueness.Heat
