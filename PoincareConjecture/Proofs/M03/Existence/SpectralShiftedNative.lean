import PoincareConjecture.Proofs.M03.Existence.SpectralTraceOperatorNative









set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*} [Countable iota] {T : ℝ}

def responseLp (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ForcingSpace iota T :=
  (memLp_responseState_of_memLp hT (Lp.memLp F) lambda).toLp (responseState lambda F)

theorem responseLp_coe (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : responseLp hT lambda F =ᵐ[timeMeasure T] responseState lambda F :=
  (memLp_responseState_of_memLp hT (Lp.memLp F) lambda).coeFn_toLp

theorem responseLp_add (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F G : ForcingSpace iota T) :
    responseLp hT lambda (F + G) = responseLp hT lambda F + responseLp hT lambda G := by
  unfold responseLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact congrArg (fun p : ResponsePath iota T => p ⟨t, Ioc_subset_Icc_self ht⟩)
    (responsePath_add hT lambda F G)

theorem responseLp_smul (hT : 0 ≤ T) (lambda : iota → NNReal)
    (a : ℝ) (F : ForcingSpace iota T) :
    responseLp hT lambda (a • F) = a • responseLp hT lambda F := by
  unfold responseLp
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact congrArg (fun p : ResponsePath iota T => p ⟨t, Ioc_subset_Icc_self ht⟩)
    (responsePath_smul hT lambda a F)

theorem norm_responseLp_le (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ‖responseLp hT lambda F‖ ≤ T * ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (norm_nonneg _))).mp
  change ‖(memLp_responseState_of_memLp hT (Lp.memLp F) lambda).toLp
    (responseState lambda F)‖ ^ 2 ≤ (T * ‖F‖) ^ 2
  rw [norm_toLp_sq, mul_pow, forcing_norm_sq]
  exact integral_response_sq_le_time_sq hT (Lp.memLp F) lambda

def responseLpLinearMap (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →ₗ[ℝ] ForcingSpace iota T where
  toFun := responseLp hT lambda
  map_add' := responseLp_add hT lambda
  map_smul' := responseLp_smul hT lambda

def responseLpOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →L[ℝ] ForcingSpace iota T :=
  (responseLpLinearMap hT lambda).mkContinuous T (fun F => by
    change ‖responseLp hT lambda F‖ ≤ T * ‖F‖
    exact norm_responseLp_le hT lambda F)

@[simp] theorem responseLpOperator_apply (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : responseLpOperator hT lambda F = responseLp hT lambda F := rfl

theorem norm_responseLpOperator_le (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ‖responseLpOperator hT lambda‖ ≤ T := by
  exact (responseLpLinearMap hT lambda).mkContinuous_norm_le hT _

def shiftedHighOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →L[ℝ] ForcingSpace iota T :=
  responseLpOperator hT lambda + generatorOperator hT lambda

theorem norm_shiftedHighOperator_le (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ‖shiftedHighOperator hT lambda‖ ≤ T + 1 :=
  (norm_add_le _ _).trans
    (add_le_add (norm_responseLpOperator_le hT lambda) (norm_generatorOperator_le hT lambda))

theorem shiftedHighOperator_coeff (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      shiftedHighOperator hT lambda F t i =
        (1 + (lambda i : ℝ)) * responseState lambda F t i := by
  have hG : generatorLp hT lambda F =ᵐ[timeMeasure T] generatorState lambda F :=
    (memLp_generatorState_of_memLp hT (Lp.memLp F) lambda).coeFn_toLp
  filter_upwards [Lp.coeFn_add (responseLp hT lambda F) (generatorLp hT lambda F),
    responseLp_coe hT lambda F, hG,
    ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda] with t hsum hu hg ha
  intro i
  change (responseLp hT lambda F + generatorLp hT lambda F) t i = _
  rw [hsum]
  change responseLp hT lambda F t i + generatorLp hT lambda F t i = _
  rw [hu, hg, ha]
  ring

private theorem shiftedInverseSqrt_bound (lambda : iota → NNReal) (i : iota) :
    |1 / Real.sqrt (1 + (lambda i : ℝ))| ≤ 1 := by
  have hpos : 0 < 1 + (lambda i : ℝ) := by positivity
  have hroot : 1 ≤ Real.sqrt (1 + (lambda i : ℝ)) := by
    have hs := Real.sq_sqrt hpos.le
    nlinarith [Real.sqrt_nonneg (1 + (lambda i : ℝ)), (lambda i).coe_nonneg]
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_one (Real.sqrt_pos.mpr hpos)).mpr hroot

private theorem shiftedRatio_bound (lambda : iota → NNReal) (i : iota) :
    |Real.sqrt (lambda i) / Real.sqrt (1 + (lambda i : ℝ))| ≤ 1 := by
  have hpos : 0 < 1 + (lambda i : ℝ) := by positivity
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one (Real.sqrt_pos.mpr hpos)).mpr
  exact Real.sqrt_le_sqrt (by linarith)

def shiftedBaseMultiplier (lambda : iota → NNReal) : State iota →L[ℝ] State iota :=
  multiplier (fun i => 1 / Real.sqrt (1 + (lambda i : ℝ))) 1 zero_le_one
    (shiftedInverseSqrt_bound lambda)

def shiftedTraceMultiplier (lambda : iota → NNReal) : State iota →L[ℝ] State iota :=
  multiplier (fun i => Real.sqrt (lambda i) / Real.sqrt (1 + (lambda i : ℝ))) 1 zero_le_one
    (shiftedRatio_bound lambda)

theorem norm_shiftedBaseMultiplier_le (lambda : iota → NNReal) (x : State iota) :
    ‖shiftedBaseMultiplier lambda x‖ ≤ ‖x‖ := by
  simpa only [shiftedBaseMultiplier, one_mul] using
    norm_multiplier_apply_le _ 1 zero_le_one (shiftedInverseSqrt_bound lambda) x

theorem norm_shiftedTraceMultiplier_le (lambda : iota → NNReal) (x : State iota) :
    ‖shiftedTraceMultiplier lambda x‖ ≤ ‖x‖ := by
  simpa only [shiftedTraceMultiplier, one_mul] using
    norm_multiplier_apply_le _ 1 zero_le_one (shiftedRatio_bound lambda) x

def shiftedTracePath (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ResponsePath iota T where
  toFun t := shiftedBaseMultiplier lambda (responsePath hT lambda F t) +
    shiftedTraceMultiplier lambda (tracePath hT lambda F t)
  continuous_toFun :=
    ((shiftedBaseMultiplier lambda).continuous.comp (responsePath hT lambda F).continuous).add
      ((shiftedTraceMultiplier lambda).continuous.comp (tracePath hT lambda F).continuous)

theorem shiftedTracePath_coeff (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) (t : Icc (0 : ℝ) T) (i : iota) :
    shiftedTracePath hT lambda F t i =
      Real.sqrt (1 + (lambda i : ℝ)) * responseState lambda F t i := by
  change 1 / Real.sqrt (1 + (lambda i : ℝ)) * responsePath hT lambda F t i +
    (Real.sqrt (lambda i) / Real.sqrt (1 + (lambda i : ℝ))) * tracePath hT lambda F t i = _
  rw [tracePath_apply_coordinate]
  have hpos : 0 < 1 + (lambda i : ℝ) := by positivity
  have hden : Real.sqrt (1 + (lambda i : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hc : 1 / Real.sqrt (1 + (lambda i : ℝ)) +
      (Real.sqrt (lambda i) / Real.sqrt (1 + (lambda i : ℝ))) * Real.sqrt (lambda i) =
        Real.sqrt (1 + (lambda i : ℝ)) := by
    field_simp
    nlinarith [Real.sq_sqrt hpos.le, Real.sq_sqrt (lambda i).coe_nonneg]
  calc
    _ = (1 / Real.sqrt (1 + (lambda i : ℝ)) +
        (Real.sqrt (lambda i) / Real.sqrt (1 + (lambda i : ℝ))) * Real.sqrt (lambda i)) *
          responsePath hT lambda F t i := by ring
    _ = _ := by rw [hc, responsePath_apply]

theorem norm_shiftedTracePath_le (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ‖shiftedTracePath hT lambda F‖ ≤ (Real.sqrt T + 1) * ‖F‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    _ ≤ ‖responsePath hT lambda F t‖ + ‖tracePath hT lambda F t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_shiftedBaseMultiplier_le _ _)
        (norm_shiftedTraceMultiplier_le _ _))
    _ ≤ ‖responsePath hT lambda F‖ + ‖tracePath hT lambda F‖ :=
      add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)
    _ ≤ Real.sqrt T * ‖F‖ + ‖F‖ :=
      add_le_add (norm_responsePath_le hT lambda F) (norm_tracePath_le hT lambda F)
    _ = _ := by ring

end PoincareConjecture.SpectralHeatNative
