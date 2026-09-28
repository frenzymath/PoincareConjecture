import PoincareConjecture.Proofs.M35.Uniqueness.Heat.StrongMixedInitial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {W H X : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [SeparableSpace X]

theorem exists_equivalent_strong_initial_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    (B : H → H → ℝ)
    (hB : ∀ u v, inner ℝ u v = inner ℝ (I (e u)) (I (e v)) + B (e u) (e v))
    {b : ℝ} (hb : 0 < b)
    (R : ℝ → H →L[ℝ] H) (hR : ContDiffOn ℝ 1 R (Icc 0 b)) (hR0 : R 0 = 0)
    (L : ℝ → H →L[ℝ] X) (hL : ContDiffOn ℝ 1 L (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ u₀ w₀ : H,
      (∀ z : H, inner ℝ (I z) (I w₀) =
        inner ℝ z (R 0 u₀) + inner ℝ (I z) (L 0 u₀) - B z u₀) →
      ∃ (u : ℝ → H) (Z : ℝ → X), u 0 = u₀ ∧ Z 0 = I w₀ ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn Z (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => I (u s)) (Z t) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, ∀ z : H, inner ℝ (I z) (Z t) =
          inner ℝ z (R t (u t)) + inner ℝ (I z) (L t (u t)) - B z (u t)) ∧
        ∃ w : ℝ → H, MemLp w 2 (SpectralHeatNative.timeMeasure T) ∧
          ∀ᵐ t ∂SpectralHeatNative.timeMeasure T, HasDerivAt u (w t) t ∧ I (w t) = Z t := by
  let E := e.toContinuousLinearMap
  let J : W →L[ℝ] X := I.comp E
  let RW : ℝ → W →L[ℝ] W := fun t => E.adjoint.comp ((R t).comp E)
  let LW : ℝ → W →L[ℝ] X := fun t => (L t).comp E
  have hJc : IsCompactOperator J := hIc.comp_clm E
  have hJd : DenseRange J := hId.comp e.surjective.denseRange I.continuous
  have hJi : Function.Injective J := hIi.comp e.injective
  have hRW : ContDiffOn ℝ 1 RW (Icc 0 b) :=
    contDiffOn_const.clm_comp (hR.clm_comp contDiffOn_const)
  have hRW0 : RW 0 = 0 := by
    simp only [RW, hR0, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  have hLW : ContDiffOn ℝ 1 LW (Icc 0 b) := hL.clm_comp contDiffOn_const
  have hpair (t : ℝ) (u z : W) (y : X) :
      inner ℝ z (J.adjoint y + mixedHeatOperator J (RW t) (LW t) u) =
        inner ℝ (I (e z)) y + B (e z) (e u) -
          inner ℝ (e z) (R t (e u)) - inner ℝ (I (e z)) (L t (e u)) := by
    simp only [inner_add_right, mixedHeatOperator, sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
      J.adjoint_inner_right, RW, E.adjoint_inner_right]
    change inner ℝ (I (e z)) y + (inner ℝ z u -
      inner ℝ (I (e z)) (I (e u)) - inner ℝ (e z) (R t (e u)) -
        inner ℝ (I (e z)) (L t (e u))) = _
    rw [hB]
    ring
  obtain ⟨T, hT, hT1, hTb, hsolve⟩ :=
    exists_strong_mixed_initial_heat J hJc hJd hJi hJn hb RW hRW hRW0 LW hLW
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro u₀ w₀ hcompat
  have hcompatW : J.adjoint (J (e.symm w₀)) +
      mixedHeatOperator J (RW 0) (LW 0) (e.symm u₀) = 0 := by
    apply ext_inner_left ℝ
    intro z
    rw [hpair, inner_zero_right, e.apply_symm_apply]
    change inner ℝ (I (e z)) (I (e (e.symm w₀))) + B (e z) u₀ -
      inner ℝ (e z) (R 0 u₀) - inner ℝ (I (e z)) (L 0 u₀) = 0
    rw [e.apply_symm_apply, hcompat]
    ring
  obtain ⟨u, Z, hu0, hZ0, hu, hZ, hd, heq, w, hw, hjet⟩ := hsolve _ _ hcompatW
  refine ⟨fun t => e (u t), Z, ?_, ?_, e.continuous.comp_continuousOn hu, hZ, hd, ?_,
    fun t => e (w t), E.comp_memLp' hw, ?_⟩
  · change e (u 0) = u₀
    rw [hu0, e.apply_symm_apply]
  · exact hZ0.trans (congrArg I (e.apply_symm_apply w₀))
  · intro t ht z
    have hp := hpair t (u t) (e.symm z) (Z t)
    rw [heq t ht, inner_zero_right, e.apply_symm_apply] at hp
    linarith only [hp]
  · filter_upwards [hjet] with t ht
    exact ⟨E.hasFDerivAt.comp_hasDerivAt t ht.1, ht.2⟩

end PoincareConjecture.M35.Uniqueness.Heat
