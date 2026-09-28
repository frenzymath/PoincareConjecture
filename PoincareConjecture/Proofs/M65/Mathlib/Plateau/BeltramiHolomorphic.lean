import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiInversion











set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ContDiff ComplexConjugate

namespace Complex



theorem differentiableAt_complex_of_beltrami_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z)
    (heq : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0) :
    DifferentiableAt ℂ f z := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hf, ?_⟩
  change fderiv ℝ f z I = I * fderiv ℝ f z 1
  have hh := congrArg (fun a : ℂ => I * a) heq
  simp only [mul_add, ← mul_assoc, I_mul_I, neg_one_mul, mul_zero] at hh
  linear_combination -hh




theorem holomorphic_inverse_of_real_differentiable (f : ℂ ≃ₜ ℂ) {z : ℂ}
    (hf : DifferentiableAt ℂ (f : ℂ → ℂ) (f.symm z))
    (hfi : DifferentiableAt ℝ (f.symm : ℂ → ℂ) z) :
    deriv (f : ℂ → ℂ) (f.symm z) ≠ 0 ∧ DifferentiableAt ℂ (f.symm : ℂ → ℂ) z := by
  let c := deriv (f : ℂ → ℂ) (f.symm z)
  let L := fderiv ℝ (f.symm : ℂ → ℂ) z
  have hprod : ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).comp L =
      ContinuousLinearMap.id ℝ ℂ := by
    have hh := ((hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp z hfi.hasFDerivAt).fderiv
    simpa only [Function.comp_def, f.apply_symm_apply, fderiv_fun_id] using hh.symm
  have hmul (v : ℂ) : L v * c = v := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hprod
  have hc : c ≠ 0 := by
    intro hzero
    have hh := hmul 1
    rw [hzero, mul_zero] at hh
    exact zero_ne_one hh
  refine ⟨hc, differentiableAt_complex_iff_differentiableAt_real.mpr ⟨hfi, ?_⟩⟩
  change L I = I * L 1
  apply mul_right_cancel₀ hc
  rw [hmul, mul_assoc, hmul, mul_one]



theorem eventually_holomorphic_of_compact_beltrami (f μ : ℂ → ℂ)
    (hf : Differentiable ℝ f) (hμ : HasCompactSupport μ)
    (heq : ∀ z, fderiv ℝ f z 1 + I * fderiv ℝ f z I =
      μ z * (fderiv ℝ f z 1 - I * fderiv ℝ f z I)) :
    ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ f z := by
  filter_upwards [hμ.compl_mem_cocompact] with z hz
  apply differentiableAt_complex_of_beltrami_zero (hf z)
  rw [heq, image_eq_zero_of_notMem_tsupport hz, zero_mul]



theorem eventually_holomorphic_inverse (f : ℂ ≃ₜ ℂ)
    (hfi : Differentiable ℝ (f.symm : ℂ → ℂ))
    (hf : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ (f : ℂ → ℂ) z) :
    ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ (f.symm : ℂ → ℂ) z := by
  filter_upwards [f.symm.isClosedEmbedding.tendsto_cocompact.eventually hf] with z hz
  exact (holomorphic_inverse_of_real_differentiable f hz (hfi z)).2




theorem smooth_beltramiReflectedHomeomorph (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hf : ContDiff ℝ ∞ (f : ℂ → ℂ)) (hfi : ContDiff ℝ ∞ (f.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (hμ : HasCompactSupport μ)
    (heq : ∀ z, fderiv ℝ (f : ℂ → ℂ) z 1 + I * fderiv ℝ (f : ℂ → ℂ) z I =
      μ z * (fderiv ℝ (f : ℂ → ℂ) z 1 - I * fderiv ℝ (f : ℂ → ℂ) z I)) :
    ContDiff ℝ ∞ (beltramiReflectedHomeomorph f hf0 : ℂ → ℂ) ∧
      ContDiff ℝ ∞ ((beltramiReflectedHomeomorph f hf0).symm : ℂ → ℂ) := by
  have hhol := eventually_holomorphic_of_compact_beltrami f μ
    (hf.differentiable (by simp)) hμ heq
  have hi := eventually_holomorphic_inverse f (hfi.differentiable (by simp)) hhol
  exact ⟨contDiff_beltramiCircleReflect f hf0 hf hhol,
    contDiff_beltramiCircleReflect f.symm
      (f.injective (by simpa only [f.apply_symm_apply] using hf0.symm)) hfi hi⟩

end Complex
