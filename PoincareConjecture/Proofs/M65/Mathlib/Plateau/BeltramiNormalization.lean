import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiGlobal

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology ContDiff SchwartzMap

namespace Complex

private def normalizePlaneHomeomorph (e : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ where
  toFun z := (e z - e 0) / (e 1 - e 0)
  invFun z := e.symm ((e 1 - e 0) * z + e 0)
  left_inv z := by
    have hd : e 1 - e 0 ≠ 0 := sub_ne_zero.mpr (e.injective.ne one_ne_zero)
    simp only [mul_div_cancel₀ _ hd, sub_add_cancel, e.symm_apply_apply]
  right_inv z := by
    have hd : e 1 - e 0 ≠ 0 := sub_ne_zero.mpr (e.injective.ne one_ne_zero)
    simp only [e.apply_symm_apply, add_sub_cancel_right, mul_div_cancel_left₀ _ hd]
  continuous_toFun := (e.continuous.sub continuous_const).div_const _
  continuous_invFun := e.symm.continuous.comp
    ((continuous_const.mul continuous_id).add continuous_const)

theorem exists_normalized_smooth_beltrami_diffeomorphism (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ e : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
      e 0 = 0 ∧ e 1 = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
        Tendsto (fderiv ℝ (e : ℂ → ℂ)) (cocompact ℂ)
          (𝓝 (c • ContinuousLinearMap.id ℝ ℂ)) ∧
        ∀ z, fderiv ℝ (e : ℂ → ℂ) z 1 + I * fderiv ℝ (e : ℂ → ℂ) z I =
          μ z * (fderiv ℝ (e : ℂ → ℂ) z 1 - I * fderiv ℝ (e : ℂ → ℂ) z I) := by
  obtain ⟨f, hf, hfi, hlim, heq⟩ := exists_smooth_beltrami_diffeomorphism μ hμ hk hbound
  have hd : f 1 - f 0 ≠ 0 := sub_ne_zero.mpr (f.injective.ne one_ne_zero)
  let c : ℂ := (f 1 - f 0)⁻¹
  let e := normalizePlaneHomeomorph f
  have he (z : ℂ) : e z = c * (f z - f 0) := by
    change (f z - f 0) / (f 1 - f 0) = _
    simp only [div_eq_mul_inv, c, mul_comm]
  have hef : (e : ℂ → ℂ) = fun z => c * (f z - f 0) := funext he
  have hD (z : ℂ) : fderiv ℝ (e : ℂ → ℂ) z = c • fderiv ℝ (f : ℂ → ℂ) z := by
    have h := ((hf.differentiable (by simp) z).hasFDerivAt.sub_const (f 0)).const_smul c
    rw [hef]
    simpa only [Pi.smul_apply, smul_eq_mul] using! h.fderiv
  refine ⟨e, ?_, ?_, ?_, ?_, c, inv_ne_zero hd, ?_, ?_⟩
  · rw [hef]
    exact contDiff_const.mul (hf.sub (contDiff_const (c := f 0)))
  · change ContDiff ℝ ∞ (fun z => f.symm ((f 1 - f 0) * z + f 0))
    exact hfi.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  · simp only [he, sub_self, mul_zero]
  · rw [he]
    exact inv_mul_cancel₀ hd
  · simpa only [funext hD] using hlim.const_smul c
  · intro z
    simp only [hD, smul_apply, smul_eq_mul]
    calc
      _ = c * (fderiv ℝ (f : ℂ → ℂ) z 1 + I * fderiv ℝ (f : ℂ → ℂ) z I) := by ring
      _ = c * (μ z * (fderiv ℝ (f : ℂ → ℂ) z 1 - I * fderiv ℝ (f : ℂ → ℂ) z I)) := by
        rw [heq]
      _ = _ := by ring

end Complex
