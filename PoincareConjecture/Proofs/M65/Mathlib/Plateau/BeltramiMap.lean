import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiPrimitive

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology ContDiff SchwartzMap ComplexConjugate

namespace Complex

private def beltramiOneForm (w b : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  w z • ContinuousLinearMap.id ℝ ℂ + b z • (conjCLE : ℂ →L[ℝ] ℂ)

private theorem contDiff_beltramiOneForm {w b : ℂ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (beltramiOneForm w b) :=
  (hw.smul contDiff_const).add (hb.smul contDiff_const)

private theorem fderiv_beltramiOneForm {w b : ℂ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hb : ContDiff ℝ ∞ b) (z u v : ℂ) :
    fderiv ℝ (beltramiOneForm w b) z u v =
      fderiv ℝ w z u * v + fderiv ℝ b z u * conj v := by
  have hd := (((hw.differentiable (by simp) z).hasFDerivAt.smul_const
    (ContinuousLinearMap.id ℝ ℂ)).add
      ((hb.differentiable (by simp) z).hasFDerivAt.smul_const
        (conjCLE : ℂ →L[ℝ] ℂ))).fderiv
  have hd' : fderiv ℝ (beltramiOneForm w b) z =
      (fderiv ℝ w z).smulRight (ContinuousLinearMap.id ℝ ℂ) +
        (fderiv ℝ b z).smulRight (conjCLE : ℂ →L[ℝ] ℂ) := by
    simpa only [beltramiOneForm, Pi.add_apply] using! hd
  rw [hd']
  rfl

private theorem symmetric_fderiv_beltramiOneForm {w b : ℂ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hb : ContDiff ℝ ∞ b)
    (hcompat : ∀ z, fderiv ℝ w z 1 + I * fderiv ℝ w z I =
      fderiv ℝ b z 1 - I * fderiv ℝ b z I) :
    ∀ z u v, fderiv ℝ (beltramiOneForm w b) z u v =
      fderiv ℝ (beltramiOneForm w b) z v u := by
  intro z u v
  have h12 : fderiv ℝ (beltramiOneForm w b) z 1 I =
      fderiv ℝ (beltramiOneForm w b) z I 1 := by
    rw [fderiv_beltramiOneForm hw hb, fderiv_beltramiOneForm hw hb]
    simp only [map_one, conj_I, mul_one]
    have hh := congrArg (fun a : ℂ => I * a) (hcompat z)
    simp only [mul_add, mul_sub, ← mul_assoc, I_mul_I, neg_one_mul] at hh
    linear_combination hh
  have hexpand (a : ℂ) : a = a.re • (1 : ℂ) + a.im • I := by
    simp only [real_smul, mul_one, re_add_im]
  rw [hexpand u, hexpand v]
  simp only [map_add, map_smul, add_apply, smul_apply, h12]
  simp only [real_smul]
  ring

theorem exists_smooth_nondegenerate_beltrami_map (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ f w : ℂ → ℂ, ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ w ∧
      Tendsto w (cocompact ℂ) (𝓝 1) ∧ (∀ z, w z ≠ 0) ∧
      (∀ z v, fderiv ℝ f z v = w z * (v + μ z * conj v)) ∧
      ∀ z, Function.Bijective (fderiv ℝ f z) := by
  obtain ⟨w, hw, hwinf, hwne, hcompat⟩ :=
    exists_smooth_beltrami_closed_coefficients μ hμ hk hbound
  let A := beltramiOneForm w (fun z => μ z * w z)
  have hA : ContDiff ℝ ∞ A := contDiff_beltramiOneForm hw ((μ.smooth ⊤).mul hw)
  have hclosed : ∀ z u v, fderiv ℝ A z u v = fderiv ℝ A z v u :=
    symmetric_fderiv_beltramiOneForm hw ((μ.smooth ⊤).mul hw) hcompat
  let f := beltramiRadialPrimitive A
  have hf : ContDiff ℝ ∞ f := contDiff_beltramiRadialPrimitive A hA hclosed
  have hformula (z v : ℂ) : fderiv ℝ f z v = w z * (v + μ z * conj v) := by
    rw [(hasFDerivAt_beltramiRadialPrimitive A hA hclosed z).fderiv]
    change w z * v + (μ z * w z) * conj v = _
    ring
  refine ⟨f, w, hf, hw, hwinf, hwne, hformula, fun z => ?_⟩
  have hinj : Function.Injective (fderiv ℝ f z) := by
    intro u v huv
    have hz : fderiv ℝ f z (u - v) = 0 := by rw [map_sub, huv, sub_self]
    rw [hformula] at hz
    have heq : u - v = -(μ z * conj (u - v)) :=
      eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hz).resolve_left (hwne z))
    have hnorm : ‖u - v‖ = ‖μ z‖ * ‖u - v‖ := by
      calc
        _ = ‖-(μ z * conj (u - v))‖ := congrArg norm heq
        _ = _ := by rw [_root_.norm_neg, norm_mul, norm_conj]
    have hle := mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg (u - v))
    have hzero : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact ⟨hinj, LinearMap.surjective_of_injective (f := (fderiv ℝ f z).toLinearMap) hinj⟩

end Complex
