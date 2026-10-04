import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth moving bumps on coordinate balls

The actual zero-extended function is an exponentially damped translate of
`expNegInvGlue (rho^2 - norm^2)`. The profile jet formulas hold at every real
argument, including the support boundary. This supports the barrier route to
Morgan--Tian Theorem 4.16; it does not assert existence of a heat solution.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace

namespace PoincareMT.RicciFlow.Splitting.MaximumPrinciple.Barrier

/-- First derivative of the flat exponential, with its zero extension. -/
def profileFirst (s : ℝ) : ℝ := s⁻¹ ^ 2 * expNegInvGlue s

/-- Second derivative of the same flat exponential. -/
def profileSecond (s : ℝ) : ℝ :=
  (s⁻¹ ^ 4 - 2 * s⁻¹ ^ 3) * expNegInvGlue s

/-- The first profile derivative is valid also at zero. -/
theorem hasDerivAt_profile (s : ℝ) :
    HasDerivAt expNegInvGlue (profileFirst s) s := by
  simpa [profileFirst] using
    expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) s

/-- The second profile derivative is valid also at zero. -/
theorem hasDerivAt_profileFirst (s : ℝ) :
    HasDerivAt profileFirst (profileSecond s) s := by
  have h : HasDerivAt profileFirst
      (s⁻¹ ^ 2 * (s⁻¹ ^ 2 - 2 * s⁻¹) * expNegInvGlue s) s := by
    have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
      (Polynomial.X ^ 2 : Polynomial ℝ) s
    simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X_pow, Polynomial.eval_C, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
    rw [Polynomial.eval_X] at h
    exact h
  apply h.congr_deriv
  unfold profileSecond
  ring

/-- The flat exponential is bounded by one. -/
theorem profile_le_one (s : ℝ) : expNegInvGlue s ≤ 1 := by
  by_cases hs : s ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hs]
    exact zero_le_one
  · simp only [expNegInvGlue, if_neg hs]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hs)))

variable {E : Type*} [NormedAddCommGroup E]

/-- Squared distance to the boundary of the ball centered at `c`. -/
def ballGap (rho : ℝ) (c x : E) : ℝ := rho ^ 2 - ‖x - c‖ ^ 2

/-- The actual moving bump, extended by zero across its moving boundary. -/
def movingBump (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x : E) : ℝ :=
  Real.exp (-C * (t - a)) * expNegInvGlue (ballGap rho (gamma t) x)

/-- Nonnegativity needs no time or damping sign restriction. -/
theorem movingBump_nonneg (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x : E) :
    0 ≤ movingBump rho C a gamma t x :=
  mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)

/-- The function is literally zero outside the open moving ball. -/
theorem movingBump_eq_zero {rho : ℝ} (C a : ℝ) (gamma : ℝ → E)
    (t : ℝ) {x : E} (hr : 0 ≤ rho) (hx : rho ≤ ‖x - gamma t‖) :
    movingBump rho C a gamma t x = 0 := by
  have hq : ballGap rho (gamma t) x ≤ 0 := by
    unfold ballGap
    nlinarith [norm_nonneg (x - gamma t)]
  simp [movingBump, expNegInvGlue.zero_of_nonpos hq]

/-- The exact center value at every time, including slab endpoints. -/
theorem movingBump_center (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) :
    movingBump rho C a gamma t (gamma t) =
      Real.exp (-C * (t - a)) * expNegInvGlue (rho ^ 2) := by
  simp [movingBump, ballGap]

/-- Every center value is strictly positive for a positive radius. -/
theorem movingBump_center_pos {rho : ℝ} (C a : ℝ) (gamma : ℝ → E)
    (t : ℝ) (hr : 0 < rho) : 0 < movingBump rho C a gamma t (gamma t) := by
  rw [movingBump_center]
  exact mul_pos (Real.exp_pos _) (expNegInvGlue.pos_of_pos (sq_pos_of_pos hr))

variable [InnerProductSpace ℝ E]

/-- Global spatial smoothness includes the moving support boundary. -/
theorem contDiff_movingBump_space (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) :
    ContDiff ℝ ∞ (movingBump rho C a gamma t) := by
  unfold movingBump ballGap
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))))

/-- A smooth center path gives joint smoothness, including zero extension. -/
theorem contDiff_movingBump (rho C a : ℝ) {gamma : ℝ → E}
    (hg : ContDiff ℝ ∞ gamma) :
    ContDiff ℝ ∞ (fun z : ℝ × E => movingBump rho C a gamma z.1 z.2) := by
  unfold movingBump ballGap
  exact (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_fst.sub contDiff_const))).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub
      ((contDiff_norm_sq ℝ).comp (contDiff_snd.sub (hg.comp contDiff_fst)))))

end PoincareMT.RicciFlow.Splitting.MaximumPrinciple.Barrier

