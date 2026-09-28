import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Profile.SmoothProfile
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.Real









set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.MetricSurgery

theorem smoothProfile_hasDerivAt {C q epsilon : ℝ} (hq : 0 < q) (s : ℝ) :
    HasDerivAt (smoothProfile C q epsilon)
      (q / s ^ 2 * smoothProfile C q epsilon s) s := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (s / q)
  simp only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero,
    mul_one, Polynomial.eval_pow, Polynomial.eval_X] at h
  convert! (h.comp s ((hasDerivAt_id s).div_const q)).const_mul (C * epsilon) using 1
  simp only [smoothProfile, inv_div]
  by_cases hs : s = 0
  · simp [hs]
  · field_simp [hq.ne', hs]

theorem smoothProfile_deriv {C q epsilon : ℝ} (hq : 0 < q) (s : ℝ) :
    deriv (smoothProfile C q epsilon) s = q / s ^ 2 * smoothProfile C q epsilon s :=
  (smoothProfile_hasDerivAt hq s).deriv

theorem smoothProfile_deriv_hasDerivAt {C q epsilon : ℝ} (hq : 0 < q) (s : ℝ) :
    HasDerivAt (deriv (smoothProfile C q epsilon))
      ((q ^ 2 / s ^ 4 - 2 * q / s ^ 3) * smoothProfile C q epsilon s) s := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    (Polynomial.X ^ 2 : Polynomial ℝ) (s / q)
  simp only [Polynomial.derivative_pow, Polynomial.derivative_X, mul_one,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  norm_num at h
  have hcomp := (h.comp s ((hasDerivAt_id s).div_const q)).const_mul
    (C * epsilon / q)
  have heq : deriv (smoothProfile C q epsilon) =
      fun x => C * epsilon / q * ((x / q)⁻¹ ^ 2 * expNegInvGlue (x / q)) := by
    funext x
    rw [smoothProfile_deriv hq]
    dsimp [smoothProfile]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hq.ne', hx]
  rw [heq]
  convert! hcomp using 1
  · simp only [Function.comp_apply, id_eq, inv_pow]
  simp only [smoothProfile]
  by_cases hs : s = 0
  · simp [hs]
  · field_simp [hq.ne', hs]

theorem smoothProfile_second_deriv {C q epsilon : ℝ} (hq : 0 < q) (s : ℝ) :
    deriv (deriv (smoothProfile C q epsilon)) s =
      (q ^ 2 / s ^ 4 - 2 * q / s ^ 3) * smoothProfile C q epsilon s :=
  (smoothProfile_deriv_hasDerivAt hq s).deriv


theorem smoothProfile_iteratedDeriv_eq_zero {C q epsilon s : ℝ}
    (hq : 0 < q) (hs : s ≤ 0) (n : ℕ) :
    iteratedDeriv n (smoothProfile C q epsilon) s = 0 := by
  have heq : Set.EqOn (smoothProfile C q epsilon) (fun _ => 0) (Set.Iic 0) :=
    fun _ hx => smoothProfile_eq_zero hq hx
  have h := iteratedDerivWithin_congr (n := n) heq hs
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic 0)
    ((smoothProfile_contDiff C q epsilon).of_le
      (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt hs] at h
  simpa using h

end PoincareConjecture.MetricSurgery
