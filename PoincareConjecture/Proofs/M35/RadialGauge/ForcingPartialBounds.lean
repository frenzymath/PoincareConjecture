import PoincareConjecture.Proofs.M35.RadialGauge.JetCalculus










set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem norm_comp_space_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : (V × ℝ) →L[ℝ] F) :
    ‖q.comp (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v)] using q.le_opNorm (v, 0)

private theorem norm_apply_scalar_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : (V × ℝ) →L[ℝ] F) : ‖q (0, 1)‖ ≤ ‖q‖ := by
  simpa only [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one, mul_one]
    using q.le_opNorm (0, 1)

theorem forcing_partial_norm_le (G : V → ℝ → ℝ) (x : V) (z : ℝ) :
    ‖forcingSpaceDeriv G x z‖ ≤ ‖iteratedFDeriv ℝ 1 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ ∧
    |forcingScalarDeriv G x z| ≤ ‖iteratedFDeriv ℝ 1 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ := by
  simp only [norm_iteratedFDeriv_one]
  refine ⟨norm_comp_space_le _, ?_⟩
  simpa only [forcingScalarDeriv, Real.norm_eq_abs] using
    norm_apply_scalar_le (fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, z))

noncomputable local instance m35ForcingPartialBoundsLocal1 :
    NormedAddCommGroup ((V × ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35ForcingPartialBoundsLocal2 :
    NormedSpace ℝ ((V × ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
noncomputable local instance m35ForcingPartialBoundsLocal3 :
    NormedAddCommGroup (V →L[ℝ] (V × ℝ)) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35ForcingPartialBoundsLocal4 :
    NormedSpace ℝ (V →L[ℝ] (V × ℝ)) := ContinuousLinearMap.toNormedSpace
noncomputable local instance m35ForcingPartialBoundsLocal5 :
    NormedAddCommGroup ((V × ℝ) →L[ℝ] V →L[ℝ] (V × ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

theorem forcing_partial_fderiv_norm_le {G : V → ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2)) (x : V) (z : ℝ) :
    ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, z)‖ ≤
        ‖iteratedFDeriv ℝ 2 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ ∧
    ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, z)‖ ≤
        ‖iteratedFDeriv ℝ 2 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ := by
  let f := fun p : V × ℝ => G p.1 p.2
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hG).2
  have hx := norm_fderiv_clm_comp_le hd
    (contDiff_const (c := ContinuousLinearMap.inl ℝ V ℝ)) (x, z)
  have hz := norm_fderiv_clm_apply_le hd (contDiff_const (c := ((0 : V), (1 : ℝ)))) (x, z)
  simp only [fderiv_fun_const, Pi.zero_apply, norm_zero, mul_zero, zero_add] at hx hz
  have hnorm : ‖fderiv ℝ (fderiv ℝ f) (x, z)‖ = ‖iteratedFDeriv ℝ 2 f (x, z)‖ := by
    simp only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
  constructor
  · exact hx.trans (by
      rw [← hnorm]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℝ V ℝ)
        (norm_nonneg (fderiv ℝ (fderiv ℝ f) (x, z))))
  · simpa only [forcingScalarDeriv, f, Prod.norm_def, norm_zero, norm_one,
      max_eq_right zero_le_one, mul_one, hnorm] using hz



theorem forcing_second_partials_norm_le {G : V → ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2)) (x : V) (z : ℝ) :
    ‖(fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, z)).comp
      (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤
        ‖iteratedFDeriv ℝ 2 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ ∧
    ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, z) (0, 1)‖ ≤
        ‖iteratedFDeriv ℝ 2 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ ∧
    ‖(fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, z)).comp
      (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤
        ‖iteratedFDeriv ℝ 2 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ ∧
    ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, z) (0, 1)‖ ≤
        ‖iteratedFDeriv ℝ 2 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ := by
  have h := forcing_partial_fderiv_norm_le hG x z
  exact ⟨(norm_comp_space_le _).trans h.1, (norm_apply_scalar_le _).trans h.1,
    (norm_comp_space_le _).trans h.2, (norm_apply_scalar_le _).trans h.2⟩

end PoincareConjecture.M35.RadialGauge
