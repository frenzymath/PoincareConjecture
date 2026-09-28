import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.FormPrimitive
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.MixedIntegral










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

theorem exists_mixed_value_initial_integral_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (R : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (L : Lp V 2 (timeMeasure T) →L[ℝ] Lp H 2 (timeMeasure T))
    (hsmall : (T + 1) * ‖R‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖L‖ < 1)
    (F : Lp V 2 (timeMeasure T)) (u₀ : H) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint u₀ +
        ∫ s in (0 : ℝ)..t, (R v) s + J.adjoint ((L v) s) + F s - v s +
          J.adjoint (J (v s)) := by
  let S := formWeakHeatOperator J hc hd hi hn hT
  let M := R + (J.adjoint.compLpL 2 (timeMeasure T)).comp L
  let A := S.comp M
  have hA : ‖A‖ < 1 := (norm_mixed_form_response_le J hc hd hi hn hT R L).trans_lt hsmall
  let p := initialFormPath J hc hd hi hn u₀
  let W := initialValuePath J hc hd hn u₀
  have hp : MemLp p 2 (timeMeasure T) := initialFormPath_memLp J hc hd hi hn hT u₀
  let p₀ := hp.toLp p
  let N : Lp V 2 (timeMeasure T) → Lp V 2 (timeMeasure T) := fun v => A v + (S F + p₀)
  have hN : ContractingWith ‖A‖₊ N := by
    refine ⟨hA, LipschitzWith.of_dist_le_mul ?_⟩
    intro v w
    simpa only [N, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub, coe_nnnorm]
      using A.le_opNorm (v - w)
  let v := hN.fixedPoint N
  let w := S (M v + F)
  have hv : v = w + p₀ := by
    have h : N v = v := hN.fixedPoint_isFixedPt
    simpa only [N, A, ContinuousLinearMap.comp_apply, w, map_add, add_assoc] using h.symm
  have hvt : ∀ᵐ s ∂timeMeasure T, v s = w s + p s := by
    rw [hv]
    filter_upwards [Lp.coeFn_add w p₀, hp.coeFn_toLp] with s hs hs'
    rw [hs, Pi.add_apply, hs']
  obtain ⟨Z, hZ0, hZc, hZv, hZi⟩ :=
    formWeakHeat_integral_value_trace J hc hd hi hn hT (M v + F)
  change ∀ᵐ s ∂timeMeasure T, J (w s) = Z s at hZv
  have hpW : ∀ᵐ s ∂timeMeasure T, J (p s) = W s :=
    initialFormPath_graph J hc hd hi hn hT u₀
  have hMcoe : ∀ᵐ s ∂timeMeasure T,
      (M v + F) s = (R v) s + J.adjoint ((L v) s) + F s := by
    have hM : M v = R v + J.adjoint.compLpL 2 (timeMeasure T) (L v) := rfl
    rw [hM]
    filter_upwards [Lp.coeFn_add (R v + J.adjoint.compLpL 2 (timeMeasure T) (L v)) F,
      Lp.coeFn_add (R v) (J.adjoint.compLpL 2 (timeMeasure T) (L v)),
      J.adjoint.coeFn_compLpL (L v)] with s hs hs' hj
    rw [hs, Pi.add_apply, hs', Pi.add_apply, hj]
  refine ⟨v, fun s => Z s + W s, ?_,
    hZc.add (initialValuePath_continuous J hc hd hn u₀).continuousOn, ?_, ?_⟩
  · change Z 0 + W 0 = u₀
    rw [hZ0, zero_add]
    exact initialValuePath_zero J hc hd hn u₀
  · filter_upwards [hvt, hZv, hpW] with s hv' hz hp'
    rw [hv', map_add, hz, hp']
  · intro t ht
    let E₀ : ℝ → V := fun s => (M v + F) s - w s + J.adjoint (J (w s))
    let E₁ : ℝ → V := fun s => -p s + J.adjoint (W s)
    have hE₀ : MemLp E₀ 2 (timeMeasure T) :=
      ((Lp.memLp (M v + F)).sub (Lp.memLp w)).add
        (J.adjoint.comp_memLp' (J.comp_memLp' (Lp.memLp w)))
    have hE₁ : MemLp E₁ 2 (timeMeasure T) := hp.neg.add
      (J.adjoint.comp_memLp' (initialValuePath_memLp J hc hd hi hn hT u₀))
    have hint (f : ℝ → V) (hf : MemLp f 2 (timeMeasure T)) :
        IntervalIntegrable f volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
        ((show IntegrableOn f (Ioc 0 T) volume from
          hf.integrable (by norm_num)).mono_set (Ioc_subset_Ioc le_rfl ht.2))
    calc
      J.adjoint (Z t + W t) = J.adjoint u₀ +
          ∫ s in (0 : ℝ)..t, E₀ s + E₁ s := by
        rw [map_add, hZi t ht, initialValuePath_integral J hc hd hi hn hT u₀ ht,
          intervalIntegral.integral_add (hint E₀ hE₀) (hint E₁ hE₁)]
        change (∫ s in (0 : ℝ)..t, E₀ s) +
          (J.adjoint u₀ + ∫ s in (0 : ℝ)..t, E₁ s) = _
        abel
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le ht.1]
        filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hvt,
          ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hMcoe,
          ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hpW]
          with s hv' hm hp'
        dsimp only [E₀, E₁]
        rw [hm, hv', ← hp', map_add, map_add]
        abel

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
