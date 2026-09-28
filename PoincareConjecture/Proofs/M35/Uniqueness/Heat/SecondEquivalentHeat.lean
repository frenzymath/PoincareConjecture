import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SecondCompatibleInitial










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

theorem exists_equivalent_second_initial_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    (B : H → H → ℝ)
    (hB : ∀ u v, inner ℝ u v = inner ℝ (I (e u)) (I (e v)) + B (e u) (e v))
    {b : ℝ} (hb : 0 < b)
    (R R₁ R₂ : ℝ → H →L[ℝ] H)
    (hR : ContDiffOn ℝ 1 R (Icc 0 b)) (hR0 : R 0 = 0)
    (hR₁ : ContDiffOn ℝ 1 R₁ (Icc 0 b)) (hR₂ : ContinuousOn R₂ (Icc 0 b))
    (hRd : ∀ t ∈ Ioo 0 b, HasDerivAt R (R₁ t) t)
    (hR₁d : ∀ t ∈ Ioo 0 b, HasDerivAt R₁ (R₂ t) t)
    (L L₁ L₂ : ℝ → H →L[ℝ] X)
    (hL : ContDiffOn ℝ 1 L (Icc 0 b))
    (hL₁ : ContDiffOn ℝ 1 L₁ (Icc 0 b)) (hL₂ : ContinuousOn L₂ (Icc 0 b))
    (hLd : ∀ t ∈ Ioo 0 b, HasDerivAt L (L₁ t) t)
    (hL₁d : ∀ t ∈ Ioo 0 b, HasDerivAt L₁ (L₂ t) t) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ u₀ w₀ z₀ : H,
      (∀ z : H, inner ℝ (I z) (I w₀) =
        inner ℝ z (R 0 u₀) + inner ℝ (I z) (L 0 u₀) - B z u₀) →
      (∀ z : H, inner ℝ (I z) (I z₀) =
        inner ℝ z (R 0 w₀) + inner ℝ (I z) (L 0 w₀) - B z w₀ +
          inner ℝ z (R₁ 0 u₀) + inner ℝ (I z) (L₁ 0 u₀)) →
      ∃ u w : ℝ → H, u 0 = u₀ ∧ w 0 = w₀ ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, ∀ z : H, inner ℝ (I z) (I (w t)) =
          inner ℝ z (R t (u t)) + inner ℝ (I z) (L t (u t)) - B z (u t) := by
  let E := e.toContinuousLinearMap
  let J : W →L[ℝ] X := I.comp E
  let RW := fun t => E.adjoint.comp ((R t).comp E)
  let LW := fun t => (L t).comp E
  let K₁ := fun t => -(E.adjoint.comp ((R₁ t).comp E)) - J.adjoint.comp ((L₁ t).comp E)
  let K₂ := fun t => -(E.adjoint.comp ((R₂ t).comp E)) - J.adjoint.comp ((L₂ t).comp E)
  have hRW : ContDiffOn ℝ 1 RW (Icc 0 b) :=
    contDiffOn_const.clm_comp (hR.clm_comp contDiffOn_const)
  have hRW0 : RW 0 = 0 := by
    simp only [RW, hR0, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  have hLW : ContDiffOn ℝ 1 LW (Icc 0 b) := hL.clm_comp contDiffOn_const
  have hK₁ : ContDiffOn ℝ 1 K₁ (Icc 0 b) :=
    (contDiffOn_const.clm_comp (hR₁.clm_comp contDiffOn_const)).neg.sub
      (contDiffOn_const.clm_comp (hL₁.clm_comp contDiffOn_const))
  have hK₂ : ContinuousOn K₂ (Icc 0 b) :=
    (continuousOn_const.clm_comp (hR₂.clm_comp continuousOn_const)).neg.sub
      (continuousOn_const.clm_comp (hL₂.clm_comp continuousOn_const))
  have hKd (t : ℝ) (ht : t ∈ Ioo 0 b) :
      HasDerivAt (fun s => mixedHeatOperator J (RW s) (LW s)) (K₁ t) t := by
    have h1 := (hasDerivAt_const t E.adjoint).clm_comp
      ((hRd t ht).clm_comp (hasDerivAt_const t E))
    have h2 := (hasDerivAt_const t J.adjoint).clm_comp
      ((hLd t ht).clm_comp (hasDerivAt_const t E))
    simpa only [mixedHeatOperator, RW, LW, K₁, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero, zero_add, add_zero, zero_sub, Pi.sub_def,
      Function.comp_def] using!
        ((hasDerivAt_const t (ContinuousLinearMap.id ℝ W - J.adjoint.comp J)).sub h1).sub h2
  have hK₁d (t : ℝ) (ht : t ∈ Ioo 0 b) : HasDerivAt K₁ (K₂ t) t := by
    have h1 := (hasDerivAt_const t E.adjoint).clm_comp
      ((hR₁d t ht).clm_comp (hasDerivAt_const t E))
    have h2 := (hasDerivAt_const t J.adjoint).clm_comp
      ((hL₁d t ht).clm_comp (hasDerivAt_const t E))
    simpa only [K₁, K₂, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
      zero_add, add_zero, Pi.neg_def, Pi.sub_def, Function.comp_def] using! h1.neg.sub h2
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
  have hpair₁ (t : ℝ) (u z : W) : inner ℝ z (K₁ t u) =
      -inner ℝ (e z) (R₁ t (e u)) - inner ℝ (I (e z)) (L₁ t (e u)) := by
    simp only [K₁, sub_apply, neg_apply, ContinuousLinearMap.comp_apply,
      inner_sub_right, inner_neg_right, E.adjoint_inner_right, J.adjoint_inner_right]
    rfl
  obtain ⟨T, hT, hT1, hTb, hsolve⟩ := exists_second_compatible_initial_heat J
    (hIc.comp_clm E) (hId.comp e.surjective.denseRange I.continuous)
    (hIi.comp e.injective) hJn hb RW hRW hRW0 LW hLW K₁ K₂ hK₁ hK₂ hKd hK₁d
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro u₀ w₀ z₀ hcompat hcompat₁
  have hinit : J.adjoint (J (e.symm w₀)) +
      mixedHeatOperator J (RW 0) (LW 0) (e.symm u₀) = 0 := by
    apply ext_inner_left ℝ
    intro z
    rw [hpair, inner_zero_right, e.apply_symm_apply]
    change inner ℝ (I (e z)) (I (e (e.symm w₀))) + B (e z) u₀ -
      inner ℝ (e z) (R 0 u₀) - inner ℝ (I (e z)) (L 0 u₀) = 0
    rw [e.apply_symm_apply, hcompat]
    ring
  have hinit₁ : J.adjoint (J (e.symm z₀)) +
      mixedHeatOperator J (RW 0) (LW 0) (e.symm w₀) + K₁ 0 (e.symm u₀) = 0 := by
    apply ext_inner_left ℝ
    intro z
    rw [inner_add_right, hpair, hpair₁, inner_zero_right,
      e.apply_symm_apply, e.apply_symm_apply]
    change inner ℝ (I (e z)) (I (e (e.symm z₀))) + B (e z) w₀ -
      inner ℝ (e z) (R 0 w₀) - inner ℝ (I (e z)) (L 0 w₀) +
        (-inner ℝ (e z) (R₁ 0 u₀) - inner ℝ (I (e z)) (L₁ 0 u₀)) = 0
    rw [e.apply_symm_apply, hcompat₁]
    ring
  obtain ⟨u, w, Z, hu0, hw0, _hZ0, hu, hw, _hZ, hdu, _hdw, heq, _hdeq⟩ :=
    hsolve (e.symm u₀) (e.symm w₀) (e.symm z₀) hinit hinit₁
  refine ⟨fun t => e (u t), fun t => e (w t), ?_, ?_,
    e.continuous.comp_continuousOn hu, e.continuous.comp_continuousOn hw, ?_, ?_⟩
  · change e (u 0) = u₀
    rw [hu0, e.apply_symm_apply]
  · change e (w 0) = w₀
    rw [hw0, e.apply_symm_apply]
  · intro t ht
    exact E.hasFDerivAt.comp_hasDerivWithinAt t (hdu t ht)
  · intro t ht z
    have hp := hpair t (u t) (e.symm z) (J (w t))
    rw [heq t ht, inner_zero_right, e.apply_symm_apply] at hp
    change 0 = inner ℝ (I z) (I (e (w t))) + B z (e (u t)) -
      inner ℝ z (R t (e (u t))) - inner ℝ (I z) (L t (e (u t))) at hp
    change inner ℝ (I z) (I (e (w t))) = inner ℝ z (R t (e (u t))) +
      inner ℝ (I z) (L t (e (u t))) - B z (e (u t))
    linarith only [hp]

end PoincareConjecture.M35.Uniqueness.Heat
