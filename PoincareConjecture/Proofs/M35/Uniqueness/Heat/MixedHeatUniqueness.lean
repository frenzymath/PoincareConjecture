import PoincareConjecture.Proofs.M35.Uniqueness.Heat.WeakResponseUniqueness
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

theorem contractive_integral_heat_unique
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    (M : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (hM : ‖(formWeakHeatOperator J hc hd hi hn hT.le).comp M‖ < 1)
    (F v w : Lp V 2 (timeMeasure T)) (U W : ℝ → H)
    (hU : ContinuousOn U (Icc 0 T)) (hW : ContinuousOn W (Icc 0 T))
    (hU0 : U 0 = W 0)
    (hUv : ∀ᵐ t ∂timeMeasure T, J (v t) = U t)
    (hWw : ∀ᵐ t ∂timeMeasure T, J (w t) = W t)
    (heqU : ∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint (U 0) +
      ∫ s in (0 : ℝ)..t, (M v) s + F s - v s + J.adjoint (J (v s)))
    (heqW : ∀ t ∈ Icc 0 T, J.adjoint (W t) = J.adjoint (W 0) +
      ∫ s in (0 : ℝ)..t, (M w) s + F s - w s + J.adjoint (J (w s))) :
    v = w ∧ ∀ t ∈ Icc 0 T, U t = W t := by
  have hQi (z : Lp V 2 (timeMeasure T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      IntervalIntegrable (fun s => (M z) s + F s - z s + J.adjoint (J (z s)))
        volume 0 t := by
    have hm := (((Lp.memLp (M z)).add (Lp.memLp F)).sub (Lp.memLp z)).add
      (J.adjoint.comp_memLp' (J.comp_memLp' (Lp.memLp z)))
    have hint : IntegrableOn (fun s => (M z) s + F s - z s + J.adjoint (J (z s)))
        (Ioc 0 T) volume := hm.integrable (by norm_num)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
    exact hint.mono_set (Ioc_subset_Ioc le_rfl ht.2)
  have hgraph : ∀ᵐ t ∂timeMeasure T, J ((v - w) t) = U t - W t := by
    filter_upwards [hUv, hWw, Lp.coeFn_sub v w] with t hu hw hdif
    rw [hdif, Pi.sub_apply, map_sub, hu, hw]
  have hdiff (t : ℝ) (ht : t ∈ Icc 0 T) : J.adjoint (U t - W t) =
      ∫ s in (0 : ℝ)..t, (M (v - w)) s - (v - w) s + J.adjoint (J ((v - w) s)) := by
    rw [map_sub, heqU t ht, heqW t ht, hU0, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hQi v ht) (hQi w ht)]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    have hMv : ∀ᵐ s ∂timeMeasure T, (M (v - w)) s = (M v) s - (M w) s := by
      rw [map_sub]
      exact Lp.coeFn_sub (M v) (M w)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl ht.2) hMv,
      ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) (Lp.coeFn_sub v w)]
      with s hm hvw
    rw [hm, hvw]
    simp only [Pi.sub_apply, map_sub]
    abel
  have hvw : v = w := sub_eq_zero.mp
    (zero_of_contractive_integral J hc hd hi hn hT M hM (v - w)
      (fun t => U t - W t) (hU.sub hW) hgraph hdiff)
  have hae : U =ᵐ[timeMeasure T] W := by
    filter_upwards [hUv, hWw] with t hu hw
    rw [← hu, ← hw, hvw]
  have he := Measure.eqOn_Ioc_of_ae_eq (volume : Measure ℝ) hae
    (hU.mono Ioc_subset_Icc_self) (hW.mono Ioc_subset_Icc_self)
  refine ⟨hvw, ?_⟩
  intro t ht
  rcases ht.1.eq_or_lt with rfl | hpos
  · exact hU0
  · exact he ⟨hpos, ht.2⟩

theorem mixed_integral_heat_unique
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    (R : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (L : Lp V 2 (timeMeasure T) →L[ℝ] Lp H 2 (timeMeasure T))
    (hsmall : (T + 1) * ‖R‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖L‖ < 1)
    (F v w : Lp V 2 (timeMeasure T)) (U W : ℝ → H)
    (hU : ContinuousOn U (Icc 0 T)) (hW : ContinuousOn W (Icc 0 T))
    (hU0 : U 0 = W 0)
    (hUv : ∀ᵐ t ∂timeMeasure T, J (v t) = U t)
    (hWw : ∀ᵐ t ∂timeMeasure T, J (w t) = W t)
    (heqU : ∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint (U 0) +
      ∫ s in (0 : ℝ)..t, ((R + (J.adjoint.compLpL 2 (timeMeasure T)).comp L) v) s +
        F s - v s + J.adjoint (J (v s)))
    (heqW : ∀ t ∈ Icc 0 T, J.adjoint (W t) = J.adjoint (W 0) +
      ∫ s in (0 : ℝ)..t, ((R + (J.adjoint.compLpL 2 (timeMeasure T)).comp L) w) s +
        F s - w s + J.adjoint (J (w s))) :
    v = w ∧ ∀ t ∈ Icc 0 T, U t = W t :=
  contractive_integral_heat_unique J hc hd hi hn hT _
    ((norm_mixed_form_response_le J hc hd hi hn hT.le R L).trans_lt hsmall)
    F v w U W hU hW hU0 hUv hWw heqU heqW

end PoincareConjecture.M35.Uniqueness.Heat
