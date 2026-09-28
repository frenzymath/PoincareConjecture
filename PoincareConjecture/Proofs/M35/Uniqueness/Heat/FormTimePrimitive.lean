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

theorem responseState_zero_parameters {ι : Type*} [Countable ι]
    {T : ℝ} (_hT : 0 ≤ T) (F : ForcingSpace ι T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    responseState (fun _ : ι => (0 : NNReal)) F t = ∫ s in (0 : ℝ)..t, F s := by
  have hF : IntervalIntegrable (fun s => F s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      ((show IntegrableOn (fun s => F s) (Ioc 0 T) volume from
        (Lp.memLp F).integrable (by norm_num)).mono_set (Ioc_subset_Ioc le_rfl ht.2))
  apply lp.ext
  funext i
  rw [responseState_apply_of_memLp (Lp.memLp F) _ ht]
  change responseCoeff (fun _ : ι => 0) F t i =
    (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i) (∫ s in (0 : ℝ)..t, F s)
  rw [← (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).intervalIntegral_comp_comm hF]
  simp only [responseCoeff, spectralMode, NNReal.coe_zero, neg_zero, zero_mul,
    Real.exp_zero, one_mul, zero_add]
  rfl

def formTimePrimitive (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J)
    {T : ℝ} (hT : 0 ≤ T) : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  exact (B.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (timeMeasure T)).comp
    ((responseLpOperator hT (fun _ => 0)).comp
      (B.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (timeMeasure T)))

theorem norm_formTimePrimitive_le (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J)
    {T : ℝ} (hT : 0 ≤ T) : ‖formTimePrimitive J hc hd hi hT‖ ≤ T := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  have hB : ‖B.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (timeMeasure T)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans B.toLinearIsometry.norm_toContinuousLinearMap_le
  have hBi : ‖B.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 (timeMeasure T)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans
      B.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hBi ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_responseLpOperator_le hT _) hB (norm_nonneg _) hT).trans_eq
        (mul_one T))) (norm_nonneg _) zero_le_one).trans_eq (one_mul T))

theorem formTimePrimitive_coe (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J)
    {T : ℝ} (hT : 0 ≤ T) (F : Lp V 2 (timeMeasure T)) :
    formTimePrimitive J hc hd hi hT F =ᵐ[timeMeasure T]
      fun t => ∫ s in (0 : ℝ)..t, F s := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (formEigenbasis J hc hd hi).repr
  let C := B.toContinuousLinearEquiv.toContinuousLinearMap
  let Q := B.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let E := C.compLpL 2 (timeMeasure T) F
  filter_upwards [Q.coeFn_compLpL (responseLpOperator hT (fun _ => 0) E),
    responseLp_coe hT (fun _ => 0) E, ae_restrict_mem measurableSet_Ioc] with t hQ hE ht
  change (Q.compLpL 2 (timeMeasure T) (responseLpOperator hT (fun _ => 0) E)) t = _
  rw [hQ, responseLpOperator_apply, hE,
    responseState_zero_parameters hT E (Ioc_subset_Icc_self ht)]
  have hEi : IntervalIntegrable (fun s => E s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr
      ((show IntegrableOn (fun s => E s) (Ioc 0 T) volume from
        (Lp.memLp E).integrable (by norm_num)).mono_set (Ioc_subset_Ioc le_rfl ht.2))
  rw [← Q.intervalIntegral_comp_comm hEi]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1.le]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl ht.2) (C.coeFn_compLpL F)] with s hs
  rw [hs]
  exact B.symm_apply_apply (F s)

end PoincareConjecture.M35.Uniqueness.Heat
