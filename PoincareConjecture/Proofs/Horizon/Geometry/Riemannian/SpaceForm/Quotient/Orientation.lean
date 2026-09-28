import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

set_option autoImplicit false

open Matrix

namespace Poincare.Geometry.Riemannian.SpaceForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_sub_one_ne_zero_of_no_unit_fixed_vector
    (A : Matrix ι ι ℝ)
    (hfree : ∀ x : EuclideanSpace ℝ ι, ‖x‖ = 1 →
      A *ᵥ WithLp.ofLp x ≠ WithLp.ofLp x) :
    (A - 1).det ≠ 0 := by
  have hfixed : ∀ x : ι → ℝ, A *ᵥ x = x → x = 0 := by
    intro x hx
    by_contra hne
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 x
    have hv : v ≠ 0 := by
      intro hz
      exact hne (congrArg WithLp.ofLp hz)
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ hn]
    apply hfree (‖v‖⁻¹ • v) hunit
    simpa only [WithLp.ofLp_smul, Matrix.mulVec_smul, v, WithLp.ofLp_toLp] using
      congrArg (fun y : ι → ℝ => ‖v‖⁻¹ • y) hx
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det (A - 1)).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  apply hfixed
  have hz : (A - 1) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hz

theorem det_eq_one_of_no_unit_fixed_vector
    (A : Matrix ι ι ℝ) (hA : A * A.transpose = 1)
    (heven : Even (Fintype.card ι))
    (hfree : ∀ x : EuclideanSpace ℝ ι, ‖x‖ = 1 →
      A *ᵥ WithLp.ofLp x ≠ WithLp.ofLp x) :
    A.det = 1 := by
  have hdet := det_sub_one_ne_zero_of_no_unit_fixed_vector A hfree
  have htranspose : (1 - A.transpose).det = (A - 1).det := by
    rw [← Matrix.det_transpose (1 - A.transpose)]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
    rw [show (1 : Matrix ι ι ℝ) - A = -(A - 1) by abel, Matrix.det_neg,
      heven.neg_one_pow, one_mul]
  have hmul : A * (1 - A.transpose) = A - 1 := by
    rw [mul_sub, mul_one, hA]
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, htranspose] at h
  exact mul_right_cancel₀ hdet (h.trans (one_mul _).symm)

end Poincare.Geometry.Riemannian.SpaceForm
