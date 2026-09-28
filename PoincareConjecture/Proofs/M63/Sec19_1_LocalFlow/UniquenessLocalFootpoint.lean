import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus











set_option autoImplicit false

open Filter
open scoped ContDiff Topology RealInnerProductSpace

namespace PoincareConjecture.M63

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



noncomputable def curveFootpointResidual (r : ℝ → E) (z : E × ℝ) : ℝ :=
  ⟪z.1 - r z.2, deriv r z.2⟫



theorem curveFootpointResidual_contDiff {r : ℝ → E} (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (curveFootpointResidual r) := by
  exact (contDiff_fst.sub (hr.comp contDiff_snd)).inner ℝ
    ((contDiff_infty_iff_deriv.mp hr).2.comp contDiff_snd)





theorem curveFootpointResidual_partial {r : ℝ → E} (hr : ContDiff ℝ ∞ r) (x : ℝ) :
    (fderiv ℝ (curveFootpointResidual r) (r x, x)).comp
        (ContinuousLinearMap.inr ℝ E ℝ) =
      (-‖deriv r x‖ ^ 2) • ContinuousLinearMap.id ℝ ℝ := by
  have hr₁ := (contDiff_infty_iff_deriv.mp hr).1
  have hr₂ := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hr).2).1
  have hpartial : HasDerivAt (fun y => curveFootpointResidual r (r x, y))
      (-‖deriv r x‖ ^ 2) x := by
    simpa only [curveFootpointResidual, Pi.sub_apply, sub_self, zero_sub, inner_zero_left,
      inner_neg_left, real_inner_self_eq_norm_sq, zero_add] using
      (((hasDerivAt_const x (r x)).sub (hr₁ x).hasDerivAt).inner ℝ
        (hr₂ x).hasDerivAt)
  have hprod : (0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.inr ℝ E ℝ := by
    apply ContinuousLinearMap.ext
    intro y
    rfl
  have hslice : HasFDerivAt (fun y => curveFootpointResidual r (r x, y))
      ((fderiv ℝ (curveFootpointResidual r) (r x, x)).comp
        (ContinuousLinearMap.inr ℝ E ℝ)) x := by
    simpa only [Function.comp_def, hprod] using
      ((curveFootpointResidual_contDiff hr).differentiable (by simp)
        (r x, x)).hasFDerivAt.comp x
          ((hasFDerivAt_const (r x) x).prodMk (hasFDerivAt_id x))
  rw [hslice.unique hpartial.hasFDerivAt]
  apply ContinuousLinearMap.ext
  intro y
  change y * (-‖deriv r x‖ ^ 2) = (-‖deriv r x‖ ^ 2) * y
  exact mul_comm _ _






theorem exists_curveFootpoint_germ [CompleteSpace E]
    {r : ℝ → E} (hr : ContDiff ℝ ∞ r) {x : ℝ} (hx : deriv r x ≠ 0) :
    ∃ pi : E → ℝ, pi (r x) = x ∧ ContDiffAt ℝ ∞ pi (r x) ∧
      (∀ᶠ z in 𝓝 (r x), curveFootpointResidual r (z, pi z) = 0) ∧
      (∀ᶠ z : E × ℝ in 𝓝 (r x, x),
        curveFootpointResidual r z = 0 ↔ pi z.1 = z.2) ∧
      (∀ᶠ y in 𝓝 x, pi (r y) = y) ∧
      HasDerivAt (fun y => pi (r y)) 1 x := by
  have hH := (curveFootpointResidual_contDiff hr).contDiffAt (x := (r x, x))
  have hc : -‖deriv r x‖ ^ 2 ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hinv : ((fderiv ℝ (curveFootpointResidual r) (r x, x)).comp
      (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [curveFootpointResidual_partial hr x]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (-‖deriv r x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext
      intro y
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]
    · apply ContinuousLinearMap.ext
      intro y
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let pi := hH.implicitFunction (by simp) hinv
  have hH0 : curveFootpointResidual r (r x, x) = 0 := by
    simp only [curveFootpointResidual, sub_self, inner_zero_left]
  have hlocal : ∀ᶠ z : E × ℝ in 𝓝 (r x, x),
      curveFootpointResidual r z = 0 ↔ pi z.1 = z.2 := by
    simpa only [hH0] using hH.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  have hreference : ∀ᶠ y in 𝓝 x, pi (r y) = y := by
    have hlim : Tendsto (fun y => (r y, y)) (𝓝 x) (𝓝 (r x, x)) :=
      hr.continuous.continuousAt.prodMk continuousAt_id
    filter_upwards [hlim.eventually hlocal] with y hy
    exact hy.mp (by simp only [curveFootpointResidual, sub_self, inner_zero_left])
  refine ⟨pi, hH.implicitFunction_apply_self (by simp) hinv,
    hH.contDiffAt_implicitFunction (by simp) hinv, ?_, hlocal, hreference, ?_⟩
  · simpa only [hH0] using hH.eventually_apply_implicitFunction (by simp) hinv
  · exact (hasDerivAt_id x).congr_of_eventuallyEq hreference

end PoincareConjecture.M63
