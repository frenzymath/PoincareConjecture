import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The unnormalized source Gaussian

The source comparison in Morgan-Tian Proposition 6.78 is
`2^n exp(-|Z|^2)`. Its actual Euclidean integral equals the book's
unnormalized reduced volume, including in dimension zero.
-/

set_option autoImplicit false

open MeasureTheory

namespace PoincareMT.ReducedVolume

/-- The real Gaussian in the actual Euclidean model is integrable in every dimension. -/
theorem euclideanGaussian_integrable (n : ℕ) :
    Integrable (fun Z : EuclideanSpace ℝ (Fin n) ↦ Real.exp (-‖Z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (ι := Fin n) (b := 1) (by norm_num) 0 0
  simpa only [zero_mul, add_zero, neg_one_mul, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, RCLike.re_eq_complex_re, Complex.exp_ofReal_re] using hc.re

/-- The precise source-space majorant used by the unnormalized reduced volume is integrable. -/
theorem sourceGaussian_integrable (n : ℕ) :
    Integrable (fun Z : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖Z‖ ^ 2)) :=
  (euclideanGaussian_integrable n).const_mul _

/-- The source Gaussian is strictly positive, including on the zero-dimensional model. -/
theorem sourceGaussian_pos (n : ℕ) (Z : EuclideanSpace ℝ (Fin n)) :
    0 < (2 : ℝ) ^ n * Real.exp (-‖Z‖ ^ 2) :=
  mul_pos (pow_pos (by norm_num) n) (Real.exp_pos _)

/-- The source Gaussian has exactly Morgan-Tian's unnormalized Euclidean mass. -/
theorem integral_sourceGaussian (n : ℕ) :
    (∫ Z : EuclideanSpace ℝ (Fin n), (2 : ℝ) ^ n * Real.exp (-‖Z‖ ^ 2)) =
      euclideanReducedVolume n := by
  have hgauss : (∫ Z : EuclideanSpace ℝ (Fin n), Real.exp (-‖Z‖ ^ 2)) =
      Real.pi ^ ((n : ℝ) / 2) := by
    simpa only [neg_one_mul, div_one, finrank_euclideanSpace, Fintype.card_fin] using
      (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin n))
        (b := 1) (by norm_num))
  have hfour : (4 : ℝ) ^ ((n : ℝ) / 2) = (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num), show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring,
      Real.rpow_natCast]
  rw [integral_const_mul, hgauss]
  delta euclideanReducedVolume
  rw [Real.rpow_eq_pow, Real.mul_rpow (by norm_num) Real.pi_pos.le, hfour]

end PoincareMT.ReducedVolume
