import PoincareConjecture.Proofs.M35.Uniqueness.Heat.MixedHeatUniqueness

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

theorem unforced_integral_heat_unique
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    (M : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (hM : ‖(formWeakHeatOperator J hc hd hi hn hT.le).comp M‖ < 1)
    (v w : Lp V 2 (timeMeasure T)) (U W : ℝ → H)
    (hU : ContinuousOn U (Icc 0 T)) (hW : ContinuousOn W (Icc 0 T))
    (hU0 : U 0 = W 0)
    (hUv : ∀ᵐ t ∂timeMeasure T, J (v t) = U t)
    (hWw : ∀ᵐ t ∂timeMeasure T, J (w t) = W t)
    (heqU : ∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint (U 0) +
      ∫ s in (0 : ℝ)..t, (M v) s - v s + J.adjoint (J (v s)))
    (heqW : ∀ t ∈ Icc 0 T, J.adjoint (W t) = J.adjoint (W 0) +
      ∫ s in (0 : ℝ)..t, (M w) s - w s + J.adjoint (J (w s))) :
    v = w ∧ ∀ t ∈ Icc 0 T, U t = W t := by
  have hadapt (z : Lp V 2 (timeMeasure T)) (Z : ℝ → H)
      (hZ : ∀ t ∈ Icc 0 T, J.adjoint (Z t) = J.adjoint (Z 0) +
        ∫ s in (0 : ℝ)..t, (M z) s - z s + J.adjoint (J (z s))) :
      ∀ t ∈ Icc 0 T, J.adjoint (Z t) = J.adjoint (Z 0) +
        ∫ s in (0 : ℝ)..t, (M z) s + (0 : Lp V 2 (timeMeasure T)) s - z s +
          J.adjoint (J (z s)) := by
    intro t ht
    rw [hZ t ht]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
      (Lp.coeFn_zero V 2 (timeMeasure T))] with s hs
    rw [hs, Pi.zero_apply, add_zero]
  exact contractive_integral_heat_unique J hc hd hi hn hT M hM 0 v w U W
    hU hW hU0 hUv hWw (hadapt v U heqU) (hadapt w W heqW)

end PoincareConjecture.M35.Uniqueness.Heat
