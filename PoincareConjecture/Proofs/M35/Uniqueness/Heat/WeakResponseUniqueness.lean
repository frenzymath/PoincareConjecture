import PoincareConjecture.Proofs.M35.Uniqueness.Heat.HomogeneousHeatUniqueness










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

theorem eq_formWeakHeat_of_integral
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    (F v : Lp V 2 (timeMeasure T)) (U : ℝ → H)
    (hU : ContinuousOn U (Icc 0 T))
    (hgraph : ∀ᵐ t ∂timeMeasure T, J (v t) = U t)
    (heq : ∀ t ∈ Icc 0 T, J.adjoint (U t) =
      ∫ s in (0 : ℝ)..t, F s - v s + J.adjoint (J (v s))) :
    v = formWeakHeatOperator J hc hd hi hn hT.le F := by
  let r := formWeakHeatOperator J hc hd hi hn hT.le F
  obtain ⟨W, _, hW, hWgraph, hWeq⟩ := formWeakHeat_integral_value_trace J hc hd hi hn hT.le F
  have hQi (z : Lp V 2 (timeMeasure T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      IntervalIntegrable (fun s => F s - z s + J.adjoint (J (z s))) volume 0 t := by
    have hm := ((Lp.memLp F).sub (Lp.memLp z)).add
      (J.adjoint.comp_memLp' (J.comp_memLp' (Lp.memLp z)))
    have hint : IntegrableOn (fun s => F s - z s + J.adjoint (J (z s)))
        (Ioc 0 T) volume := hm.integrable (by norm_num)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
    exact hint.mono_set (Ioc_subset_Ioc le_rfl ht.2)
  have hdiff (t : ℝ) (ht : t ∈ Icc 0 T) :
      J.adjoint (U t - W t) =
        ∫ s in (0 : ℝ)..t, -(v s - r s) + J.adjoint (J (v s - r s)) := by
    rw [map_sub, heq t ht, hWeq t ht, ← intervalIntegral.integral_sub (hQi v ht) (hQi r ht)]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [map_sub]
    abel
  have hzero := form_homogeneous_integral_zero J hc hd hi hT
    (fun s => v s - r s) ((Lp.memLp v).sub (Lp.memLp r))
    (fun s => U s - W s) (hU.sub hW) (by
      filter_upwards [hgraph, hWgraph] with s hs hs'
      rw [map_sub, hs, hs']) hdiff
  apply Lp.ext
  filter_upwards [hzero.2] with s hs
  exact sub_eq_zero.mp hs

theorem zero_of_contractive_integral
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    (M : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (hM : ‖(formWeakHeatOperator J hc hd hi hn hT.le).comp M‖ < 1)
    (v : Lp V 2 (timeMeasure T)) (U : ℝ → H)
    (hU : ContinuousOn U (Icc 0 T))
    (hgraph : ∀ᵐ t ∂timeMeasure T, J (v t) = U t)
    (heq : ∀ t ∈ Icc 0 T, J.adjoint (U t) =
      ∫ s in (0 : ℝ)..t, (M v) s - v s + J.adjoint (J (v s))) : v = 0 := by
  have hv := eq_formWeakHeat_of_integral J hc hd hi hn hT (M v) v U hU hgraph heq
  let A := (formWeakHeatOperator J hc hd hi hn hT.le).comp M
  have he : A v = v := hv.symm
  have hb := A.le_opNorm v
  rw [he] at hb
  apply norm_eq_zero.mp
  nlinarith only [hb, hM, norm_nonneg v]

end PoincareConjecture.M35.Uniqueness.Heat
