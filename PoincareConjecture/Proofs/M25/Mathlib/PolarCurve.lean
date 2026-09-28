import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring











set_option autoImplicit false

namespace Real




theorem polar_parameters_eq_of_mem_Icc
    {a b r1 r2 theta1 theta2 : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2)
    (htheta1 : theta1 ∈ Set.Icc a b)
    (htheta2 : theta2 ∈ Set.Icc a b)
    (hwidth : b - a < 2 * Real.pi)
    (heq : (r1 * Real.cos theta1, r1 * Real.sin theta1) =
      (r2 * Real.cos theta2, r2 * Real.sin theta2)) :
    r1 = r2 ∧ theta1 = theta2 := by
  have hsum (r theta : ℝ) :
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  have hsq : r1 ^ 2 = r2 ^ 2 := by
    calc
      r1 ^ 2 = (r1 * Real.cos theta1) ^ 2 + (r1 * Real.sin theta1) ^ 2 :=
        (hsum r1 theta1).symm
      _ = (r2 * Real.cos theta2) ^ 2 + (r2 * Real.sin theta2) ^ 2 :=
        congrArg (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) heq
      _ = r2 ^ 2 := hsum r2 theta2
  have hr : r1 = r2 := (sq_eq_sq₀ hr1.le hr2.le).mp hsq
  rw [← hr] at heq
  have hcos : Real.cos theta1 = Real.cos theta2 :=
    mul_left_cancel₀ hr1.ne' (congrArg Prod.fst heq)
  have hsin : Real.sin theta1 = Real.sin theta2 :=
    mul_left_cancel₀ hr1.ne' (congrArg Prod.snd heq)
  have hcosSub : Real.cos (theta1 - theta2) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    nlinarith only [Real.cos_sq_add_sin_sq theta2]
  have hleft : -(2 * Real.pi) < theta1 - theta2 := by
    linarith only [htheta1.1, htheta2.2, hwidth]
  have hright : theta1 - theta2 < 2 * Real.pi := by
    linarith only [htheta1.2, htheta2.1, hwidth]
  exact ⟨hr, sub_eq_zero.mp
    ((Real.cos_eq_one_iff_of_lt_of_lt hleft hright).mp hcosSub)⟩




theorem polar_deriv_ne_zero_of_pos
    (R theta : ℝ → ℝ) (t : ℝ)
    (hR : DifferentiableAt ℝ R t)
    (htheta : DifferentiableAt ℝ theta t)
    (hRpos : 0 < R t) (hthetapos : 0 < deriv theta t) :
    deriv (fun s : ℝ =>
      (R s * Real.cos (theta s), R s * Real.sin (theta s))) t ≠ 0 := by
  have hx := hR.hasDerivAt.mul htheta.hasDerivAt.cos
  have hy := hR.hasDerivAt.mul htheta.hasDerivAt.sin
  have hpair := hx.prodMk hy
  intro hzero
  have hcoordinates :
      (deriv R t * Real.cos (theta t) + R t * (-Real.sin (theta t) * deriv theta t),
        deriv R t * Real.sin (theta t) + R t * (Real.cos (theta t) * deriv theta t)) =
          (0 : ℝ × ℝ) := hpair.deriv.symm.trans hzero
  have hxzero :
      deriv R t * Real.cos (theta t) + R t * (-Real.sin (theta t) * deriv theta t) = 0 :=
    congrArg Prod.fst hcoordinates
  have hyzero :
      deriv R t * Real.sin (theta t) + R t * (Real.cos (theta t) * deriv theta t) = 0 :=
    congrArg Prod.snd hcoordinates
  have hdet :
      Real.cos (theta t) *
          (deriv R t * Real.sin (theta t) + R t * (Real.cos (theta t) * deriv theta t)) -
        Real.sin (theta t) *
          (deriv R t * Real.cos (theta t) + R t * (-Real.sin (theta t) * deriv theta t)) =
        R t * deriv theta t := by
    calc
      _ = R t * deriv theta t *
          (Real.cos (theta t) ^ 2 + Real.sin (theta t) ^ 2) := by ring
      _ = R t * deriv theta t := by rw [Real.cos_sq_add_sin_sq, mul_one]
  have hprodZero : R t * deriv theta t = 0 := by
    rw [← hdet, hxzero, hyzero, mul_zero, mul_zero, sub_zero]
  exact (mul_pos hRpos hthetapos).ne' hprodZero

end Real
