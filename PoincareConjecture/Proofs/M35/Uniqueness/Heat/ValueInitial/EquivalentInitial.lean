import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.NonautonomousInitial









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {W H X : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [SeparableSpace X]

theorem exists_equivalent_value_initial_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    (B : H → H → ℝ)
    (hB : ∀ u v, inner ℝ u v = inner ℝ (I (e u)) (I (e v)) + B (e u) (e v))
    {T M A C : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (he : ‖e.toContinuousLinearMap‖ ≤ M)
    (R : ℝ → H →L[ℝ] H) (hRc : ContinuousOn R (Icc 0 T))
    (hRb : ∀ t ∈ Icc 0 T, ‖R t‖ ≤ A)
    (L : ℝ → H →L[ℝ] X) (hLc : ContinuousOn L (Icc 0 T))
    (hLb : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * (M * (A * M)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * (C * M) < 1) (u₀ : X) :
    ∃ (v : ℝ → H) (U : ℝ → X),
      MemLp v 2 (timeMeasure T) ∧ U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, I (v t) = U t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ w : H,
        HasDerivWithinAt (fun s => inner ℝ (I w) (U s))
          (inner ℝ w (R t (v t)) + inner ℝ (I w) (L t (v t)) - B w (v t))
            (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, ∀ w : H,
        inner ℝ (I w) (U t) = inner ℝ (I w) u₀ +
          ∫ s in (0 : ℝ)..t, inner ℝ w (R s (v s)) +
            inner ℝ (I w) (L s (v s)) - B w (v s)) := by
  let E := e.toContinuousLinearMap
  let J : W →L[ℝ] X := I.comp E
  let RW : ℝ → W →L[ℝ] W := fun t => E.adjoint.comp ((R t).comp E)
  let LW : ℝ → W →L[ℝ] X := fun t => (L t).comp E
  have hJc : IsCompactOperator J := hIc.comp_clm E
  have hJd : DenseRange J := hId.comp e.surjective.denseRange I.continuous
  have hJi : Function.Injective J := hIi.comp e.injective
  have hRWc : ContinuousOn RW (Icc 0 T) :=
    continuousOn_const.clm_comp (hRc.clm_comp continuousOn_const)
  have hLWc : ContinuousOn LW (Icc 0 T) := hLc.clm_comp continuousOn_const
  let : SecondCountableTopologyEither ℝ (W →L[ℝ] W) := ⟨Or.inl inferInstance⟩
  let : SecondCountableTopologyEither ℝ (W →L[ℝ] X) := ⟨Or.inl inferInstance⟩
  have hRm : AEStronglyMeasurable RW (timeMeasure T) :=
    (hRWc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hLm : AEStronglyMeasurable LW (timeMeasure T) :=
    (hLWc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hRa : ∀ᵐ t ∂timeMeasure T, ‖RW t‖ ≤ M * (A * M) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc
      ‖RW t‖ ≤ ‖E.adjoint‖ * ‖(R t).comp E‖ := E.adjoint.opNorm_comp_le _
      _ ≤ M * (A * M) := mul_le_mul
        (by simpa only [LinearIsometryEquiv.norm_map] using he)
        (((R t).opNorm_comp_le E).trans
          (mul_le_mul (hRb t (Ioc_subset_Icc_self ht)) he (norm_nonneg _) hA))
        (norm_nonneg _) hM
  have hLa : ∀ᵐ t ∂timeMeasure T, ‖LW t‖ ≤ C * M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ((L t).opNorm_comp_le E).trans
      (mul_le_mul (hLb t (Ioc_subset_Icc_self ht)) he (norm_nonneg _) hC)
  obtain ⟨v, U, hU0, hUc, hUv, hweak, hUi⟩ :=
    exists_nonautonomous_value_initial_heat J hJc hJd hJi hJn hT
      (by positivity) (by positivity) RW hRm hRa LW hLm hLa hsmall 0 u₀
  have hew (w : H) : J (e.symm w) = I w := by
    change I (e (e.symm w)) = I w
    rw [e.apply_symm_apply]
  have hrt (w : H) (t : ℝ) :
      inner ℝ (e.symm w) (RW t (v t)) = inner ℝ w (R t (e (v t))) := by
    change inner ℝ (e.symm w) (E.adjoint (R t (e (v t)))) = _
    rw [E.adjoint_inner_right]
    change inner ℝ (e (e.symm w)) _ = _
    rw [e.apply_symm_apply]
  have henergy (w : H) (t : ℝ) : inner ℝ (e.symm w) (v t) -
      inner ℝ (J (e.symm w)) (J (v t)) = B w (e (v t)) := by
    rw [hB, e.apply_symm_apply, hew]
    change inner ℝ (I w) (I (e (v t))) + B w (e (v t)) -
      inner ℝ (I w) (I (e (v t))) = _
    exact add_sub_cancel_left _ _
  refine ⟨fun t => e (v t), U, E.comp_memLp' (Lp.memLp v), hU0, hUc, hUv, ?_, ?_⟩
  · filter_upwards [hweak, Lp.coeFn_zero W 2 (timeMeasure T)] with t ht hz
    intro w
    have h := ht (e.symm w)
    rw [hz, Pi.zero_apply, add_zero, hrt, henergy, hew] at h
    exact h
  · intro t ht w
    let D : ℝ → W := fun s => RW s (v s) + J.adjoint (LW s (v s)) +
      (0 : Lp W 2 (timeMeasure T)) s - v s + J.adjoint (J (v s))
    have hD : MemLp D 2 (timeMeasure T) :=
      ((((memLp_timeDependent_apply hRm hRa v).add
        (J.adjoint.comp_memLp' (memLp_timeDependent_apply hLm hLa v))).add
        (Lp.memLp (0 : Lp W 2 (timeMeasure T)))).sub (Lp.memLp v)).add
        (J.adjoint.comp_memLp' (J.comp_memLp' (Lp.memLp v)))
    have hDi : IntervalIntegrable D volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
        ((show IntegrableOn D (Ioc 0 T) volume from hD.integrable (by norm_num)).mono_set
          (Ioc_subset_Ioc le_rfl ht.2))
    have hpair (z : X) : inner ℝ (e.symm w) (J.adjoint z) = inner ℝ (I w) z := by
      rw [J.adjoint_inner_right, hew]
    calc
      inner ℝ (I w) (U t) = inner ℝ (I w) u₀ +
          ∫ s in (0 : ℝ)..t, inner ℝ (e.symm w) (D s) := by
        rw [← hpair, hUi t ht, inner_add_right, hpair]
        congr 1
        exact ((innerSL ℝ (e.symm w)).intervalIntegral_comp_comm hDi).symm
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le ht.1]
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
          (Ioc_subset_Ioc le_rfl ht.2) (Lp.coeFn_zero W 2 (timeMeasure T))] with s hs
        simp only [D, hs, Pi.zero_apply, add_zero, inner_add_right, inner_sub_right,
          hrt, J.adjoint_inner_right, hew]
        have hE := henergy w s
        rw [hew] at hE
        change inner ℝ w (R s (e (v s))) + inner ℝ (I w) (L s (e (v s))) -
          inner ℝ (e.symm w) (v s) + inner ℝ (I w) (J (v s)) = _
        linarith only [hE]

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
