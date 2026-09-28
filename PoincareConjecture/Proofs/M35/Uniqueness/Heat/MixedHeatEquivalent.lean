import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousMixedInitial









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {W H X : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [SeparableSpace X]

theorem exists_equivalent_continuous_mixed_initial_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    (B : H → H → ℝ)
    (hB : ∀ u v, inner ℝ u v = inner ℝ (I (e u)) (I (e v)) + B (e u) (e v))
    {b : ℝ} (hb : 0 < b)
    (R : ℝ → H →L[ℝ] H) (hRc : ContinuousOn R (Icc 0 b)) (hR0 : R 0 = 0)
    (L : ℝ → H →L[ℝ] X) (hLc : ContinuousOn L (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ v₀ : H,
      ∃ (v : ℝ → H) (U : ℝ → X),
        MemLp v 2 (timeMeasure T) ∧ U 0 = I v₀ ∧ ContinuousOn U (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T, I (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ w : H,
          HasDerivWithinAt (fun s => inner ℝ (I w) (U s))
            (inner ℝ w (R t (v t)) + inner ℝ (I w) (L t (v t)) - B w (v t))
              (Icc 0 T) t) := by
  let E := e.toContinuousLinearMap
  let J : W →L[ℝ] X := I.comp E
  let RW : ℝ → W →L[ℝ] W := fun t => E.adjoint.comp ((R t).comp E)
  let LW : ℝ → W →L[ℝ] X := fun t => (L t).comp E
  have hJc : IsCompactOperator J := hIc.comp_clm E
  have hJd : DenseRange J := hId.comp e.surjective.denseRange I.continuous
  have hJi : Function.Injective J := hIi.comp e.injective
  have hRWc : ContinuousOn RW (Icc 0 b) :=
    continuousOn_const.clm_comp (hRc.clm_comp continuousOn_const)
  have hRW0 : RW 0 = 0 := by
    simp only [RW, hR0, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  have hLWc : ContinuousOn LW (Icc 0 b) := hLc.clm_comp continuousOn_const
  obtain ⟨T, hT, hT1, hTb, hsolve⟩ :=
    exists_continuous_mixed_initial_heat J hJc hJd hJi hJn hb RW hRWc hRW0 LW hLWc
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro v₀
  obtain ⟨v, U, hv, hU0, hUc, hUv, hweak⟩ := hsolve (e.symm v₀)
  have hew (w : H) : J (e.symm w) = I w := by
    change I (e (e.symm w)) = I w
    rw [e.apply_symm_apply]
  refine ⟨fun t => e (v t), U, E.comp_memLp' hv, ?_, hUc, hUv, ?_⟩
  · exact hU0.trans (hew v₀)
  · filter_upwards [hweak] with t ht
    intro w
    have hrt : inner ℝ (e.symm w) (RW t (v t)) = inner ℝ w (R t (e (v t))) := by
      change inner ℝ (e.symm w) (E.adjoint (R t (e (v t)))) = _
      rw [E.adjoint_inner_right]
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
