import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormWeakHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

omit [SeparableSpace H] in
private theorem sqrt_parameter_shift (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hn : ‖J‖ ≤ 1) (i : EigenIndex J) :
    Real.sqrt i.1.val * (1 + (generatorParameters J hc hd hn i : ℝ)) =
      Real.sqrt (1 + (generatorParameters J hc hd hn i : ℝ)) := by
  let q := 1 + (generatorParameters J hc hd hn i : ℝ)
  have hq : 0 ≤ q := by positivity
  have h := sqrt_eigenparameter_mul_shifted J hc hd hn i
  calc
    Real.sqrt i.1.val * q = Real.sqrt i.1.val * (Real.sqrt q * Real.sqrt q) := by
      rw [Real.mul_self_sqrt hq]
    _ = Real.sqrt q := by rw [← mul_assoc, h, one_mul]

theorem formDualResponse_value_trace (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace (EigenIndex J) T) :
    ∃ U : ℝ → H, U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      (∀ᵐ t ∂timeMeasure T, J (formDualResponseOperator J hc hd hi hn hT F t) = U t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖U t‖ ≤ (Real.sqrt T + 1) * ‖F‖) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let lambda := generatorParameters J hc hd hn
  let B := (eigenbasis J hc hd).repr
  let Q : State (EigenIndex J) →L[ℝ] H := B.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let U := fun t => Q (shiftedBaseMultiplier lambda (responseState lambda F t) +
    shiftedTraceMultiplier lambda (SpectralTraceNative.traceState lambda F t))
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      U t = B.symm (shiftedTracePath hT lambda F ⟨t, ht⟩) := rfl
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · simp only [U, responseState_zero, SpectralTraceNative.traceState_zero hT (Lp.memLp F),
      map_zero, add_zero]
  · exact Q.continuous.comp_continuousOn
      (((shiftedBaseMultiplier lambda).continuous.comp_continuousOn
        (continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda)).add
          ((shiftedTraceMultiplier lambda).continuous.comp_continuousOn
            (SpectralTraceNative.continuousOn_traceState hT (Lp.memLp F) lambda)))
  · filter_upwards [formDualResponseOperator_coe J hc hd hi hn hT F,
      shiftedHighOperator_coeff hT lambda F, ae_restrict_mem measurableSet_Ioc]
      with t hvt hst ht
    rw [heq t (Ioc_subset_Icc_self ht)]
    apply B.injective
    apply lp.ext
    funext i
    rw [hvt, repr_inclusion_decode, LinearIsometryEquiv.apply_symm_apply, hst,
      shiftedTracePath_coeff, ← mul_assoc, sqrt_parameter_shift J hc hd hn]
  · intro t ht
    rw [heq t ht, LinearIsometryEquiv.norm_map]
    exact (ContinuousMap.norm_coe_le_norm _ _).trans (norm_shiftedTracePath_le hT lambda F)

theorem formWeakHeat_value_trace (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : Lp V 2 (timeMeasure T)) :
    ∃ U : ℝ → H, U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      (∀ᵐ t ∂timeMeasure T, J (formWeakHeatOperator J hc hd hi hn hT F t) = U t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖U t‖ ≤ (Real.sqrt T + 1) * ‖F‖) := by
  let B := (formEigenbasis J hc hd hi).repr
  let C := B.toContinuousLinearEquiv.toContinuousLinearMap
  let E := C.compLpL 2 (timeMeasure T) F
  have hE : ‖E‖ ≤ ‖F‖ := by
    exact (C.norm_compLp_le F).trans
      ((mul_le_mul_of_nonneg_right B.toLinearIsometry.norm_toContinuousLinearMap_le
        (norm_nonneg F)).trans_eq (one_mul _))
  obtain ⟨U, hU0, hUc, hgraph, hb⟩ := formDualResponse_value_trace J hc hd hi hn hT E
  exact ⟨U, hU0, hUc, hgraph, fun t ht =>
    (hb t ht).trans (mul_le_mul_of_nonneg_left hE (by positivity))⟩

end PoincareConjecture.M35.Uniqueness.Heat
