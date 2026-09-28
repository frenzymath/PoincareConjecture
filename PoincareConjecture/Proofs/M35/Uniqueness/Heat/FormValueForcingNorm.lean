import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormValueForcing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

omit [CompleteSpace V] in
private theorem norm_timeLp_le_of_bound {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (v : Lp V 2 (timeMeasure T)) (hv : ∀ᵐ t ∂timeMeasure T, ‖v t‖ ≤ C) :
    ‖v‖ ≤ Real.sqrt T * C := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hC)).mp
  have he : ‖v‖ ^ 2 = ∫ t, ‖v t‖ ^ 2 ∂timeMeasure T := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [he, mul_pow, Real.sq_sqrt hT]
  calc
    _ ≤ ∫ _t, C ^ 2 ∂timeMeasure T := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm (Lp.memLp v).1).mp (Lp.memLp v))
        (integrable_const _)
      exact hv.mono (fun t ht => pow_le_pow_left₀ (norm_nonneg _) ht 2)
    _ = T * C ^ 2 := by
      simp [timeMeasure, integral_const, Measure.real, Real.volume_Ioc, hT, ENNReal.toReal_ofReal]

def formValueHeatOperator (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) : Lp H 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T) :=
  (formWeakHeatOperator J hc hd hi hn hT).comp (J.adjoint.compLpL 2 (timeMeasure T))

theorem norm_formValueHeatOperator_le (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖formValueHeatOperator J hc hd hi hn hT‖ ≤ Real.sqrt T * (Real.sqrt T + 1) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  let BF := (formEigenbasis J hc hd hi).repr
  let BH := (eigenbasis J hc hd).repr
  let CH := BH.toContinuousLinearEquiv.toContinuousLinearMap
  let G := CH.compLpL 2 (timeMeasure T) F
  have hG : ‖G‖ ≤ ‖F‖ := (CH.norm_compLp_le F).trans
    ((mul_le_mul_of_nonneg_right BH.toLinearIsometry.norm_toContinuousLinearMap_le
      (norm_nonneg F)).trans_eq (one_mul _))
  have hp : ∀ᵐ t ∂timeMeasure T,
      ‖formValueHeatOperator J hc hd hi hn hT F t‖ ≤ (Real.sqrt T + 1) * ‖F‖ := by
    filter_upwards [formWeakHeat_value_forcing_trace J hc hd hi hn hT F,
      ae_restrict_mem measurableSet_Ioc] with t ht htime
    rw [← BF.norm_map]
    change ‖BF (formWeakHeatOperator J hc hd hi hn hT
      (J.adjoint.compLpL 2 (timeMeasure T) F) t)‖ ≤ _
    rw [ht (Ioc_subset_Icc_self htime)]
    exact ((ContinuousMap.norm_coe_le_norm _ _).trans
      (norm_shiftedTracePath_le hT _ G)).trans
        (mul_le_mul_of_nonneg_left hG (by positivity))
  have hb := norm_timeLp_le_of_bound hT (show 0 ≤ (Real.sqrt T + 1) * ‖F‖ by positivity)
    (formValueHeatOperator J hc hd hi hn hT F) hp
  simpa only [mul_assoc] using hb

end PoincareConjecture.M35.Uniqueness.Heat
