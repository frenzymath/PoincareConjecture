import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormWeakHeat










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

def formDualPrimitive (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (F : ForcingSpace (EigenIndex J) T) (t : ℝ) : V :=
  (formEigenbasis J hc hd hi).repr.symm
    (responseState (generatorParameters J hc hd hn) F t)

omit [SeparableSpace H] in
@[simp] theorem formDualPrimitive_zero (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (F : ForcingSpace (EigenIndex J) T) :
    formDualPrimitive J hc hd hi hn F 0 = 0 := by
  simp only [formDualPrimitive, responseState_zero, map_zero]

theorem continuousOn_formDualPrimitive (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace (EigenIndex J) T) :
    ContinuousOn (formDualPrimitive J hc hd hi hn F) (Icc 0 T) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  exact (formEigenbasis J hc hd hi).repr.symm.continuous.comp_continuousOn
    (continuousOn_responseState_of_memLp hT (Lp.memLp F) _)

theorem formDualPrimitive_graph (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace (EigenIndex J) T) :
    ∀ᵐ t ∂timeMeasure T,
      J.adjoint (J (formDualResponseOperator J hc hd hi hn hT F t)) =
        formDualPrimitive J hc hd hi hn F t := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  let lambda := generatorParameters J hc hd hn
  filter_upwards [formDualResponseOperator_coe J hc hd hi hn hT F,
    shiftedHighOperator_coeff hT lambda F] with t hvt hst
  apply B.injective
  apply lp.ext
  funext i
  rw [form_repr_adjoint_inclusion, hvt, LinearIsometryEquiv.apply_symm_apply, hst]
  change i.1.val * ((1 + (lambda i : ℝ)) * responseState lambda F t i) =
    B (B.symm (responseState lambda F t)) i
  rw [LinearIsometryEquiv.apply_symm_apply, ← mul_assoc]
  have hp : (1 + (lambda i : ℝ)) * i.1.val = 1 :=
    parameter_resolvent_identity i.1.val (eigenparameter_pos J hc hd i)
      (eigenparameter_le_one J hc hd hn i)
  rw [mul_comm i.1.val, hp, one_mul]

theorem formDualPrimitive_integral (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace (EigenIndex J) T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    formDualPrimitive J hc hd hi hn F t =
      ∫ s in (0 : ℝ)..t,
        (formEigenbasis J hc hd hi).repr.symm (F s) -
          formDualResponseOperator J hc hd hi hn hT F s +
            J.adjoint (J (formDualResponseOperator J hc hd hi hn hT F s)) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  let Q : State (EigenIndex J) →L[ℝ] V := B.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let lambda := generatorParameters J hc hd hn
  have hD : IntervalIntegrable (derivativeState lambda F) volume 0 t :=
    (intervalIntegrable_derivativeState_of_memLp hT (Lp.memLp F) lambda).mono_set
      (by simpa only [uIcc_of_le hT, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl ht.2)
  have he : ∀ᵐ s ∂timeMeasure T,
      Q (derivativeState lambda F s) = B.symm (F s) -
        formDualResponseOperator J hc hd hi hn hT F s +
          J.adjoint (J (formDualResponseOperator J hc hd hi hn hT F s)) := by
    filter_upwards [formDualResponseOperator_coe J hc hd hi hn hT F,
      shiftedHighOperator_coeff hT lambda F,
      formDualPrimitive_graph J hc hd hi hn hT F,
      derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda,
      ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda] with s hv hs hg heq hgen
    rw [hg]
    apply B.injective
    apply lp.ext
    funext i
    simp only [map_sub, map_add, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply]
    rw [hv]
    change B (B.symm (derivativeState lambda F s)) i = B (B.symm (F s)) i -
      B (B.symm (shiftedHighOperator hT lambda F s)) i +
        B (B.symm (responseState lambda F s)) i
    simp only [LinearIsometryEquiv.apply_symm_apply]
    rw [hs]
    change derivativeState lambda F s i = F s i -
      (1 + (lambda i : ℝ)) * responseState lambda F s i + responseState lambda F s i
    have h := congrArg (fun z : State (EigenIndex J) => z i) heq
    change derivativeState lambda F s i + generatorState lambda F s i = F s i at h
    rw [hgen] at h
    linarith only [h]
  calc
    formDualPrimitive J hc hd hi hn F t = ∫ s in (0 : ℝ)..t, Q (derivativeState lambda F s) :=
      (Q.intervalIntegral_comp_comm hD).symm
    _ = _ := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le ht.1]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Ioc_subset_Ioc le_rfl ht.2) he] with s hs
      exact hs

end PoincareConjecture.M35.Uniqueness.Heat
