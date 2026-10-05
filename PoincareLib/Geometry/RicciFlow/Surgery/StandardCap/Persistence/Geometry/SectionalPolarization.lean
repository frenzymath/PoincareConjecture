import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Geometry.CurvaturePolarization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Curvature forms from orthonormal plane values

Orthogonal projection and normalization reduce arbitrary plane values
to orthonormal pairs, including the dependent and zero-vector cases.
This is the algebra behind the curvature-one model in Morgan--Tian,
Definition 9.76; see M44 derivation 28.
-/

set_option autoImplicit false
-- Subtraction of four-linear forms needs the nested module instances.
set_option maxSynthPendingDepth 8

namespace PoincareMT.M44

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Vanishing on orthonormal planes implies vanishing on every plane.
No dimension or completeness assumption is needed. Source: the
sectional-curvature polarization in M44 derivation 28. -/
theorem curvatureForm_planes_zero_of_orthonormal
    (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hunit : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 → R u v u v = 0)
    (u v : E) : R u v u v = 0 := by
  have horth (a b : E) (hab : inner ℝ a b = 0) : R a b a b = 0 := by
    by_cases ha : a = 0
    · subst a
      simp
    by_cases hb : b = 0
    · subst b
      simp
    have h := hunit (‖a‖⁻¹ • a) (‖b‖⁻¹ • b)
      (norm_smul_inv_norm ha) (norm_smul_inv_norm hb)
      (by simp only [real_inner_smul_left, inner_smul_right, hab, mul_zero])
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero,
      inv_eq_zero, norm_eq_zero, ha, hb, false_or] using h
  have hfstzero (a b c : E) : R a a b c = 0 := by
    linarith only [hfirst a a b c]
  have hlstzero (a b c : E) : R a b c c = 0 := by
    linarith only [hlast a b c c]
  by_cases hu : u = 0
  · subst u
    simp
  have huu : inner ℝ u u ≠ 0 := (real_inner_self_pos.mpr hu).ne'
  let w := v - (inner ℝ u v / inner ℝ u u) • u
  have huw : inner ℝ u w = 0 := by
    dsimp [w]
    rw [inner_sub_right, inner_smul_right]
    rw [div_mul_cancel₀ _ huu, sub_self]
  have h := horth u w huw
  simpa only [w, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hfstzero, hlstzero, mul_zero, sub_zero] using h

/-- Orthonormal plane values determine an algebraic curvature form.
Source: Morgan--Tian pp. 5-7, used for Definition 9.76. -/
theorem curvatureForm_zero_of_orthonormal
    (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hcyclic : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hunit : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 → R u v u v = 0)
    (a b c d : E) : R a b c d = 0 := by
  apply curvatureForm_eq_zero_of_planes R hfirst hpair hcyclic
  apply curvatureForm_planes_zero_of_orthonormal R hfirst
  · intro u v w z
    rw [hpair u v w z, hfirst w z u v, hpair z w u v]
  · exact hunit

end PoincareMT.M44
