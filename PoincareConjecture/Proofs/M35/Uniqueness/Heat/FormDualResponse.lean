import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormDualCoordinates

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

def formDualResponseOperator (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    ForcingSpace (EigenIndex J) T →L[ℝ] Lp V 2 (timeMeasure T) := by
  letI : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  exact (B.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (timeMeasure T)).comp
    (shiftedHighOperator hT (generatorParameters J hc hd hn))

theorem formDualResponseOperator_coe (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace (EigenIndex J) T) :
    letI : Countable (EigenIndex J) := eigenIndex_countable J hc
    formDualResponseOperator J hc hd hi hn hT F =ᵐ[timeMeasure T]
      fun t => (formEigenbasis J hc hd hi).repr.symm
        (shiftedHighOperator hT (generatorParameters J hc hd hn) F t) := by
  exact ContinuousLinearMap.coeFn_compLpL
    ((formEigenbasis J hc hd hi).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap) _

theorem norm_formDualResponseOperator_le (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖formDualResponseOperator J hc hd hi hn hT‖ ≤ T + 1 := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  have hB : ‖B.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    B.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (ContinuousLinearMap.norm_compLpL_le _ |>.trans hB)
      (norm_shiftedHighOperator_le hT _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _))

theorem formDualResponse_weak_equation (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace (EigenIndex J) T) :
    ∃ P D : ℝ → V,
      P 0 = 0 ∧ ContinuousOn P (Icc (0 : ℝ) T) ∧ MemLp D 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt P (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T,
        J.adjoint (J (formDualResponseOperator J hc hd hi hn hT F t)) = P t) ∧
      (∀ᵐ t ∂timeMeasure T,
        D t + formDualResponseOperator J hc hd hi hn hT F t - P t =
          (formEigenbasis J hc hd hi).repr.symm (F t)) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  let Q : State (EigenIndex J) →L[ℝ] V := B.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let lambda := generatorParameters J hc hd hn
  let P := fun t => Q (responseState lambda F t)
  let D := fun t => Q (derivativeState lambda F t)
  have hv := formDualResponseOperator_coe J hc hd hi hn hT F
  have hs := shiftedHighOperator_coeff hT lambda F
  refine ⟨P, D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [P, responseState_zero, map_zero]
  · exact Q.continuous.comp_continuousOn
      (continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda)
  · exact Q.comp_memLp' (memLp_derivativeState_of_memLp hT (Lp.memLp F) lambda)
  · filter_upwards [ae_hasDerivAt_responseState_of_memLp hT (Lp.memLp F) lambda] with t ht
    exact Q.hasFDerivAt.comp_hasDerivAt t ht
  · filter_upwards [hv, hs] with t hvt hst
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
  · filter_upwards [hv, hs,
      derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda,
      ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda] with t hvt hst heq hg
    apply B.injective
    apply lp.ext
    funext i
    simp only [map_sub, map_add, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply]
    rw [hvt, LinearIsometryEquiv.apply_symm_apply, hst]
    simp only [D, P, Q, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply]
    simp only [B, LinearIsometryEquiv.apply_symm_apply]
    change derivativeState lambda F t i + (1 + (lambda i : ℝ)) * responseState lambda F t i -
      responseState lambda F t i = F t i
    have he := congrArg (fun z : State (EigenIndex J) => z i) heq
    change derivativeState lambda F t i + generatorState lambda F t i = F t i at he
    rw [hg] at he
    linarith only [he]

end PoincareConjecture.M35.Uniqueness.Heat
