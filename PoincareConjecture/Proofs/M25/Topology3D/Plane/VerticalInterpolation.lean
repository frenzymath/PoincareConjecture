import PoincareConjecture.Proofs.M25.Topology3D.Plane.ParametricInverse
import Mathlib.Topology.Algebra.Support












set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*}



def verticalInterpolation (f : E × ℝ → ℝ) (tau : E → ℝ) (p : E × ℝ) : E × ℝ :=
  (p.1, lineInterpolation (fun x => f (p.1, x)) (tau p.1) p.2)



theorem verticalInterpolation_eq_self_of_zero {f : E × ℝ → ℝ} {tau : E → ℝ}
    {p : E × ℝ} (htau : tau p.1 = 0) : verticalInterpolation f tau p = p := by
  simp [verticalInterpolation, htau]



theorem verticalInterpolation_eq_self_of_fixed {f : E × ℝ → ℝ} {tau : E → ℝ}
    {p : E × ℝ} (hf : f p = p.2) : verticalInterpolation f tau p = p := by
  apply Prod.ext
  · rfl
  · exact lineInterpolation_eq_self (f := fun x => f (p.1, x)) hf (tau p.1)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem contDiff_familyLineInterpolation {f : E × ℝ → ℝ} {tau : E → ℝ}
    {n : ℕ∞ω} (hf : ContDiff ℝ n f) (htau : ContDiff ℝ n tau) :
    ContDiff ℝ n (fun p : E × ℝ =>
      lineInterpolation (fun x => f (p.1, x)) (tau p.1) p.2) := by
  exact ((contDiff_const.sub (htau.comp contDiff_fst)).mul contDiff_snd).add
    ((htau.comp contDiff_fst).mul hf)



theorem contDiff_verticalInterpolation {f : E × ℝ → ℝ} {tau : E → ℝ}
    {n : ℕ∞ω} (hf : ContDiff ℝ n f) (htau : ContDiff ℝ n tau) :
    ContDiff ℝ n (verticalInterpolation f tau) :=
  contDiff_fst.prodMk (contDiff_familyLineInterpolation hf htau)




noncomputable def verticalInterpolationDiffeomorph [CompleteSpace E]
    {f : E × ℝ → ℝ} {tau : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (htau : ContDiff ℝ ∞ tau)
    (htau_range : ∀ z, tau z ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ z x, 0 < deriv (fun y => f (z, y)) x)
    (a b : ℝ) (hfix : ∀ z x, x ≤ a ∨ b ≤ x → f (z, x) = x) :
    (E × ℝ) ≃ₘ[ℝ] (E × ℝ) := by
  apply fiberDiffeomorph (contDiff_familyLineInterpolation hf htau)
  · intro z x
    have hslice : Differentiable ℝ (fun y => f (z, y)) :=
      (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    rw [(hasDerivAt_lineInterpolation (hslice x).hasDerivAt (tau z)).deriv]
    exact lineInterpolation_derivative_pos (hpos z x) (htau_range z)
  · intro z
    exact surjective_lineInterpolation
      (hf.continuous.comp (continuous_const.prodMk continuous_id)) a b (hfix z) (tau z)



@[simp] theorem verticalInterpolationDiffeomorph_apply [CompleteSpace E]
    {f : E × ℝ → ℝ} {tau : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (htau : ContDiff ℝ ∞ tau)
    (htau_range : ∀ z, tau z ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ z x, 0 < deriv (fun y => f (z, y)) x)
    (a b : ℝ) (hfix : ∀ z x, x ≤ a ∨ b ≤ x → f (z, x) = x) (p : E × ℝ) :
    verticalInterpolationDiffeomorph hf htau htau_range hpos a b hfix p =
      verticalInterpolation f tau p := rfl



theorem hasCompactSupport_verticalInterpolation_sub_id
    {f : ℝ × ℝ → ℝ} {tau : ℝ → ℝ} (a b c d : ℝ)
    (hfix : ∀ z x, x ≤ a ∨ b ≤ x → f (z, x) = x)
    (hzero : ∀ z, z ≤ c ∨ d ≤ z → tau z = 0) :
    HasCompactSupport (fun p => verticalInterpolation f tau p - p) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc c d ×ˢ Icc a b))
  intro p hp
  apply sub_eq_zero.mpr
  by_cases hz : p.1 ∈ Icc c d
  · apply verticalInterpolation_eq_self_of_fixed
    apply hfix
    by_contra hout
    push Not at hout
    exact hp ⟨hz, hout.1.le, hout.2.le⟩
  · apply verticalInterpolation_eq_self_of_zero
    apply hzero
    by_contra hout
    push Not at hout
    exact hz ⟨hout.1.le, hout.2.le⟩

end PoincareConjecture.M25.Topology3D
