import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereFixedDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Set Filter
open scoped Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fixedHyperplane_normal_ne_zero (A : E →L[ℝ] E) (x : E) (hx : ‖x‖ = 1)
    (hA : ∀ v, ⟪x, v⟫_ℝ = 0 → A v = v) (hi : Function.Injective A) :
    ⟪x, A x⟫_ℝ ≠ 0 := by
  intro hz
  have hAx : A x = x := hi (hA (A x) hz)
  rw [hAx, real_inner_self_eq_norm_sq, hx, one_pow] at hz
  exact one_ne_zero hz

theorem fderiv_normal_pos_of_local_exterior (f : E → E) {x : E} (hx : ‖x‖ = 1)
    (hf : DifferentiableAt ℝ f x)
    (hfixed : ∀ᶠ y in 𝓝 x, ‖y‖ = 1 → f y = y)
    (hi : Function.Injective (fderiv ℝ f x))
    (hout : ∀ᶠ y in 𝓝 x, 1 ≤ ‖y‖ → 1 ≤ ‖f y‖) :
    0 < ⟪x, fderiv ℝ f x x⟫_ℝ := by
  have hfx : f x = x := hfixed.self_of_nhds hx
  have hne := fixedHyperplane_normal_ne_zero (fderiv ℝ f x) x hx
    (fun v hv => fderiv_eq_of_local_fixed_sphere f x v hx hf hfixed hv) hi
  let γ : ℝ → E := fun t => (1 + t) • x
  have hγ0 : γ 0 = x := by simp only [γ, add_zero, one_smul]
  have hγ : HasDerivAt γ x 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x
  have hF : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by
    rw [hγ0]
    exact hf.hasFDerivAt
  have hg : HasDerivAt (fun t => ‖f (γ t)‖ ^ 2)
      (2 * ⟪x, fderiv ℝ f x x⟫_ℝ) 0 := by
    simpa only [Function.comp_def, hγ0, hfx] using (hF.comp_hasDerivAt 0 hγ).norm_sq
  have hcont : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa only [hγ0] using hγ.continuousAt.tendsto
  have hnonneg : 0 ≤ 2 * ⟪x, fderiv ℝ f x x⟫_ℝ := by
    apply ge_of_tendsto hg.tendsto_slope_zero_right
    filter_upwards [(hcont.eventually hout).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htpos
    have ht0 : 0 < t := htpos
    have hγnorm : 1 ≤ ‖γ t‖ := by
      simp only [γ, norm_smul, Real.norm_eq_abs, hx, mul_one,
        abs_of_pos (by linarith : 0 < 1 + t)]
      linarith
    have hn := ht hγnorm
    have hs : 0 ≤ ‖f (γ t)‖ ^ 2 - 1 := by nlinarith [norm_nonneg (f (γ t))]
    simpa only [zero_add, hγ0, hfx, hx, one_pow, smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr ht0.le) hs
  exact lt_of_le_of_ne (by linarith) (Ne.symm hne)

end PoincareConjecture.M25.Topology3D
