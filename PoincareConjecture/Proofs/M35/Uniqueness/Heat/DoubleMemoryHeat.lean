import PoincareConjecture.Proofs.M35.Uniqueness.Heat.MemoryHeat

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

theorem formTimePrimitive_twice_coe (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J)
    {T : ℝ} (hT : 0 ≤ T) (v : Lp V 2 (timeMeasure T)) :
    formTimePrimitive J hc hd hi hT (formTimePrimitive J hc hd hi hT v) =ᵐ[timeMeasure T]
      fun t => ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, v r := by
  let Q := formTimePrimitive J hc hd hi hT
  filter_upwards [formTimePrimitive_coe J hc hd hi hT (Q v),
    ae_restrict_mem measurableSet_Ioc] with t ht hmem
  rw [ht]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hmem.1.le]
  exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl hmem.2)
    (formTimePrimitive_coe J hc hd hi hT v)

theorem exists_double_memory_integral_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C D E : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (B : ℝ → V →L[ℝ] V) (hBm : AEStronglyMeasurable B (timeMeasure T))
    (hBb : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ D)
    (N : ℝ → V →L[ℝ] V) (hNm : AEStronglyMeasurable N (timeMeasure T))
    (hNb : ∀ᵐ t ∂timeMeasure T, ‖N t‖ ≤ E)
    (hsmall : (T + 1) * (A + D * T + E * (T * T)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (F : Lp V 2 (timeMeasure T)) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = 0 ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U t) =
        ∫ s in (0 : ℝ)..t, R s (v s) + J.adjoint (L s (v s)) +
          B s (∫ r in (0 : ℝ)..s, v r) +
          N s (∫ r in (0 : ℝ)..s, ∫ q in (0 : ℝ)..r, v q) +
          F s - v s + J.adjoint (J (v s)) := by
  let RR := timeDependentLpOperator hRm hRb
  let LL := timeDependentLpOperator hLm hLb
  let BB := timeDependentLpOperator hBm hBb
  let NN := timeDependentLpOperator hNm hNb
  let Q := formTimePrimitive J hc hd hi hT
  let M := RR + BB.comp Q + NN.comp (Q.comp Q)
  have hBQ : ‖BB.comp Q‖ ≤ D * T :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_timeDependentLpOperator_le hBm hBb hD)
        (norm_formTimePrimitive_le J hc hd hi hT) (norm_nonneg _) hD)
  have hQQ : ‖Q.comp Q‖ ≤ T * T :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_formTimePrimitive_le J hc hd hi hT)
        (norm_formTimePrimitive_le J hc hd hi hT) (norm_nonneg _) hT)
  have hNQ : ‖NN.comp (Q.comp Q)‖ ≤ E * (T * T) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_timeDependentLpOperator_le hNm hNb hE) hQQ (norm_nonneg _) hE)
  have hM : ‖M‖ ≤ A + D * T + E * (T * T) :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans
        (add_le_add (norm_timeDependentLpOperator_le hRm hRb hA) hBQ)) hNQ)
  have hs : (T + 1) * ‖M‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖LL‖ < 1 :=
    (add_le_add (mul_le_mul_of_nonneg_left hM (by positivity))
      (mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hLm hLb hC)
        (by positivity))).trans_lt hsmall
  obtain ⟨v, U, hU0, hUc, hUv, hUi⟩ :=
    exists_mixed_integral_heat J hc hd hi hn hT M LL hs F
  refine ⟨v, U, hU0, hUc, hUv, ?_⟩
  have hMv : M v = (RR v + BB (Q v)) + NN (Q (Q v)) := rfl
  have he : ∀ᵐ s ∂timeMeasure T,
      (M v) s = R s (v s) + B s (∫ r in (0 : ℝ)..s, v r) +
        N s (∫ r in (0 : ℝ)..s, ∫ q in (0 : ℝ)..r, v q) ∧
        (LL v) s = L s (v s) := by
    rw [hMv]
    filter_upwards [Lp.coeFn_add (RR v + BB (Q v)) (NN (Q (Q v))),
      Lp.coeFn_add (RR v) (BB (Q v)),
      timeDependentLpOperator_coe hRm hRb v,
      timeDependentLpOperator_coe hBm hBb (Q v),
      timeDependentLpOperator_coe hNm hNb (Q (Q v)),
      formTimePrimitive_coe J hc hd hi hT v,
      formTimePrimitive_twice_coe J hc hd hi hT v,
      timeDependentLpOperator_coe hLm hLb v] with s hs hs' hr hb hn hq hqq hl
    rw [hs, Pi.add_apply, hs', Pi.add_apply, hr, hb, hn, hq, hqq]
    exact ⟨rfl, hl⟩
  intro t ht
  rw [hUi t ht]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl ht.2) he] with s hs
  rw [hs.1, hs.2]
  abel

end PoincareConjecture.M35.Uniqueness.Heat
