import PoincareConjecture.Proofs.M35.Uniqueness.CoordinateRotation02
import Mathlib.Analysis.SpecialFunctions.Complex.Arg








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Matrix

namespace PoincareConjecture.M35.Uniqueness

theorem exists_rotation_angle {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ t : ℝ, Real.cos t = c ∧ Real.sin t = s := by
  let z : ℂ := ⟨c, s⟩
  have hn : ‖z‖ = 1 := by
    have hsq : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      change c * c + s * s = 1
      nlinarith only [h]
    nlinarith [norm_nonneg z]
  refine ⟨Complex.arg z, ?_, ?_⟩
  · simpa only [hn, one_mul] using Complex.norm_mul_cos_arg z
  · simpa only [hn, one_mul] using Complex.norm_mul_sin_arg z

theorem coordinateRotation_apply (s : ℝ) (x : StandardCapSpace) :
    standardRotation (coordinateRotation s) x =
      WithLp.toLp 2 ![Real.cos s * x 0 - Real.sin s * x 1,
        Real.sin s * x 0 + Real.cos s * x 1, x 2] := by
  ext i
  fin_cases i <;> simp [standardRotation, coordinateRotation, dotProduct,
    Fin.sum_univ_succ, sub_eq_add_neg]

theorem coordinateRotation02_apply (s : ℝ) (x : StandardCapSpace) :
    standardRotation (coordinateRotation02 s) x =
      WithLp.toLp 2 ![Real.cos s * x 0 - Real.sin s * x 2, x 1,
        Real.sin s * x 0 + Real.cos s * x 2] := by
  ext i
  fin_cases i <;> simp [standardRotation, coordinateRotation02, dotProduct,
    Fin.sum_univ_succ, sub_eq_add_neg]

theorem exists_two_coordinate_rotations_axis (x : StandardCapSpace) (hx : ‖x‖ = 1) :
    ∃ a b : ℝ, standardRotation (coordinateRotation a * coordinateRotation02 b)
      (EuclideanSpace.single 2 1) = x := by
  let z : ℂ := ⟨-x 0, -x 1⟩
  let r := ‖z‖
  have hr : r ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simp only [r, Complex.sq_norm, Complex.normSq_apply, z]
    ring
  have hx' : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq x
    rw [hx] at h
    simpa only [one_pow, Fin.sum_univ_three] using h.symm
  obtain ⟨b, hbcos, hbsin⟩ := exists_rotation_angle (c := x 2) (s := r) (by linarith)
  let a := Complex.arg z
  have hac : r * Real.cos a = -x 0 := Complex.norm_mul_cos_arg z
  have has : r * Real.sin a = -x 1 := Complex.norm_mul_sin_arg z
  refine ⟨a, b, ?_⟩
  rw [standardRotation_mul, coordinateRotation02_apply, coordinateRotation_apply]
  ext i
  fin_cases i
  · change Real.cos a * (Real.cos b * 0 - Real.sin b * 1) - Real.sin a * 0 = x 0
    rw [hbsin]
    nlinarith only [hac]
  · change Real.sin a * (Real.cos b * 0 - Real.sin b * 1) + Real.cos a * 0 = x 1
    rw [hbsin]
    nlinarith only [has]
  · change Real.sin b * 0 + Real.cos b * 1 = x 2
    simp only [hbcos, mul_zero, mul_one, zero_add]

end PoincareConjecture.M35.Uniqueness
