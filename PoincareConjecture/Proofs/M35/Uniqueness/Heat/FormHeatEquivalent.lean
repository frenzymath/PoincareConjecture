import PoincareConjecture.Proofs.M35.Uniqueness.Heat.NonautonomousFormHeat









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {W H X : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [SecondCountableTopology X]

private theorem norm_adjoint_sandwich_le (e : W →L[ℝ] H) (L : H →L[ℝ] H) :
    ‖e.adjoint.comp (L.comp e)‖ ≤ ‖e‖ ^ 2 * ‖L‖ := by
  calc
    _ ≤ ‖e.adjoint‖ * ‖L.comp e‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖e.adjoint‖ * (‖L‖ * ‖e‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = ‖e‖ ^ 2 * ‖L‖ := by rw [LinearIsometryEquiv.norm_map]; ring

theorem exists_equivalent_nonautonomous_tolerance (I : H →L[ℝ] X)
    (hIc : IsCompactOperator I) (hId : DenseRange I) (hIi : Function.Injective I)
    (e : W ≃L[ℝ] H) (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    (B : H → H → ℝ)
    (hB : ∀ u v, inner ℝ u v = inner ℝ (I (e u)) (I (e v)) + B (e u) (e v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ, 0 ≤ T → T ≤ 1 →
      ∀ R : ℝ → H →L[ℝ] H, AEStronglyMeasurable R (timeMeasure T) →
      (∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ δ) →
      ∀ F : ℝ → H, MemLp F 2 (timeMeasure T) →
      ∃ (v : ℝ → H) (U : ℝ → X),
        MemLp v 2 (timeMeasure T) ∧ U 0 = 0 ∧ ContinuousOn U (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T, I (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ w : H,
          HasDerivWithinAt (fun s => inner ℝ (I w) (U s))
            (inner ℝ w (R t (v t) + F t) - B w (v t)) (Icc 0 T) t) := by
  let L := e.toContinuousLinearMap
  let J : W →L[ℝ] X := I.comp L
  have hJc : IsCompactOperator J := hIc.comp_clm L
  have hJd : DenseRange J := hId.comp e.surjective.denseRange I.continuous
  have hJi : Function.Injective J := hIi.comp e.injective
  let q := ‖L‖ ^ 2
  let δ := 1 / (4 * (q + 1))
  have hq : 0 ≤ q := sq_nonneg _
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδid : 4 * (q + 1) * δ = 1 := by
    dsimp only [δ]
    exact mul_one_div_cancel (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro T hT hT1 R hRm hRb F hF
  let RW : ℝ → W →L[ℝ] W := fun t => L.adjoint.comp ((R t).comp L)
  have hRWm : AEStronglyMeasurable RW (timeMeasure T) := by
    have hc : Continuous (fun Q : H →L[ℝ] H => L.adjoint.comp (Q.comp L)) :=
      continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
    exact hc.comp_aestronglyMeasurable hRm
  have hRWb : ∀ᵐ t ∂timeMeasure T, ‖RW t‖ ≤ q * δ := by
    filter_upwards [hRb] with t ht
    exact (norm_adjoint_sandwich_le L (R t)).trans (mul_le_mul_of_nonneg_left ht hq)
  have hsmall : (T + 1) * (q * δ) < 1 := by
    have hmul := mul_le_mul_of_nonneg_right (show T + 1 ≤ 2 by linarith)
      (mul_nonneg hq hδ.le)
    nlinarith only [hmul, hδid, hδ]
  have hFW : MemLp (fun t => L.adjoint (F t)) 2 (timeMeasure T) := L.adjoint.comp_memLp' hF
  let FW := hFW.toLp (fun t => L.adjoint (F t))
  obtain ⟨v, U, hU0, hUc, hUv, hweak⟩ :=
    exists_nonautonomous_form_heat J hJc hJd hJi hJn hT (mul_nonneg hq hδ.le)
      RW hRWm hRWb hsmall FW
  refine ⟨fun t => e (v t), U, L.comp_memLp' (Lp.memLp v), hU0, hUc, hUv, ?_⟩
  filter_upwards [hweak, hFW.coeFn_toLp] with t ht hFt
  intro w
  have hew : J (e.symm w) = I w := by
    change I (e (e.symm w)) = _
    rw [e.apply_symm_apply]
  have hrt : inner ℝ (e.symm w) (RW t (v t) + FW t) =
      inner ℝ w (R t (e (v t)) + F t) := by
    rw [hFt]
    change inner ℝ (e.symm w) (L.adjoint (R t (e (v t))) + L.adjoint (F t)) = _
    rw [← map_add, L.adjoint_inner_right]
    change inner ℝ (e (e.symm w)) _ = _
    rw [e.apply_symm_apply]
  have henergy : inner ℝ (e.symm w) (v t) -
      inner ℝ (J (e.symm w)) (J (v t)) = B w (e (v t)) := by
    rw [hB, e.apply_symm_apply, hew]
    change inner ℝ (I w) (I (e (v t))) + B w (e (v t)) -
      inner ℝ (I w) (I (e (v t))) = _
    exact add_sub_cancel_left _ _
  have h := ht (e.symm w)
  rw [hrt, henergy, hew] at h
  exact h

end PoincareConjecture.M35.Uniqueness.Heat
