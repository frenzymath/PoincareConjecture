import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Centered.SpectralResponse

/-!
# The actual closed trace of the initial spectral response

M03's continuous shifted trace adds to the initial heat path in the
trace space itself. MT2007 Claim 19.1, p. 437; contract review block 8
and `2026-09-21-uncut-centered-response.md`, statements 1-2.
-/

set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareMT.M63

open SpectralHeatNative QuasilinearDeTurckNative

variable {iota : Type*} [Countable iota] (lambda : iota → NNReal)
  (w : State iota) {T : ℝ}

/-- The initial heat path plus the actual continuous response trace,
defined on the entire closed time interval. MT2007 Claim 19.1, p. 437;
uncut centered response derivation, item 1. -/
noncomputable def initialResponseTrace (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    ResponsePath iota T where
  toFun t := heat lambda (t : ℝ).toNNReal w + shiftedTracePath hT lambda F t
  continuous_toFun :=
    ((continuous_heat_apply lambda w).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)).add
      (shiftedTracePath hT lambda F).continuous

/-- The closed trace retains the exact initial data, base response,
uniform deviation bound and common-a.e. high-state identity. MT2007
Claim 19.1, p. 437; uncut centered response derivation, item 2. -/
theorem initialResponseTrace_spec (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    initialResponseTrace lambda w hT F ⟨0, le_rfl, hT⟩ = w ∧
      (∀ t : Icc (0 : ℝ) T,
        shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F t) =
          heat lambda (t : ℝ).toNNReal (shiftedBaseMultiplier lambda w) +
            responseState lambda F t) ∧
      (∀ t : Icc (0 : ℝ) T,
        ‖initialResponseTrace lambda w hT F t - heat lambda (t : ℝ).toNNReal w‖ ≤
          (Real.sqrt T + 1) * ‖F‖) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
        shiftedBaseMultiplier lambda
          (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t) =
            initialResponseTrace lambda w hT F ⟨t, ht⟩ := by
  have hzero : shiftedTracePath hT lambda F ⟨0, le_rfl, hT⟩ = 0 := by
    apply lp.ext
    funext i
    rw [shiftedTracePath_coeff]
    simp only [responseState_zero, lp.coeFn_zero, Pi.zero_apply, mul_zero]
  have hcomm (t : NNReal) :
      shiftedBaseMultiplier lambda (heat lambda t w) =
        heat lambda t (shiftedBaseMultiplier lambda w) := by
    apply lp.ext
    funext i
    simp only [shiftedBaseMultiplier, multiplier_apply, heat_apply]
    ring
  have htrace (t : Icc (0 : ℝ) T) :
      shiftedBaseMultiplier lambda (shiftedTracePath hT lambda F t) =
        responseState lambda F t := by
    apply lp.ext
    funext i
    change 1 / Real.sqrt (1 + (lambda i : ℝ)) * shiftedTracePath hT lambda F t i = _
    rw [shiftedTracePath_coeff, one_div, ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity : 0 < 1 + (lambda i : ℝ))).ne', one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change heat lambda (0 : ℝ).toNNReal w + shiftedTracePath hT lambda F ⟨0, le_rfl, hT⟩ = w
    simp only [hzero, Real.toNNReal_zero, heat_zero, ContinuousLinearMap.id_apply, add_zero]
  · intro t
    change shiftedBaseMultiplier lambda
      (heat lambda (t : ℝ).toNNReal w + shiftedTracePath hT lambda F t) = _
    rw [map_add, hcomm, htrace]
  · intro t
    change ‖heat lambda (t : ℝ).toNNReal w + shiftedTracePath hT lambda F t -
      heat lambda (t : ℝ).toNNReal w‖ ≤ _
    rw [add_sub_cancel_left]
    exact ((shiftedTracePath hT lambda F).norm_coe_le_norm t).trans
      (norm_shiftedTracePath_le hT lambda F)
  · filter_upwards [intermediate_high_eq_trace hT lambda F,
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    intro htmem
    change shiftedBaseMultiplier lambda
      (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t) =
        heat lambda t.toNNReal w + shiftedTracePath hT lambda F ⟨t, htmem⟩
    rw [map_add, (initialHeatHigh_trace lambda w hmem.1).1, ht htmem]

end PoincareMT.M63
