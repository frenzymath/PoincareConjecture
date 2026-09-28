import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.Barrier

def profileFirst (s : ℝ) : ℝ := s⁻¹ ^ 2 * expNegInvGlue s

def profileSecond (s : ℝ) : ℝ :=
  (s⁻¹ ^ 4 - 2 * s⁻¹ ^ 3) * expNegInvGlue s

theorem hasDerivAt_profile (s : ℝ) :
    HasDerivAt expNegInvGlue (profileFirst s) s := by
  simpa [profileFirst] using
    expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) s

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

theorem profile_le_one (s : ℝ) : expNegInvGlue s ≤ 1 := by
  by_cases hs : s ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hs]
    exact zero_le_one
  · simp only [expNegInvGlue, if_neg hs]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hs)))

variable {E : Type*} [NormedAddCommGroup E]

def ballGap (rho : ℝ) (c x : E) : ℝ := rho ^ 2 - ‖x - c‖ ^ 2

def movingBump (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x : E) : ℝ :=
  Real.exp (-C * (t - a)) * expNegInvGlue (ballGap rho (gamma t) x)

theorem movingBump_nonneg (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x : E) :
    0 ≤ movingBump rho C a gamma t x :=
  mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)

theorem movingBump_eq_zero {rho : ℝ} (C a : ℝ) (gamma : ℝ → E)
    (t : ℝ) {x : E} (hr : 0 ≤ rho) (hx : rho ≤ ‖x - gamma t‖) :
    movingBump rho C a gamma t x = 0 := by
  have hq : ballGap rho (gamma t) x ≤ 0 := by
    unfold ballGap
    nlinarith [norm_nonneg (x - gamma t)]
  simp [movingBump, expNegInvGlue.zero_of_nonpos hq]

theorem movingBump_center (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) :
    movingBump rho C a gamma t (gamma t) =
      Real.exp (-C * (t - a)) * expNegInvGlue (rho ^ 2) := by
  simp [movingBump, ballGap]

theorem movingBump_center_pos {rho : ℝ} (C a : ℝ) (gamma : ℝ → E)
    (t : ℝ) (hr : 0 < rho) : 0 < movingBump rho C a gamma t (gamma t) := by
  rw [movingBump_center]
  exact mul_pos (Real.exp_pos _) (expNegInvGlue.pos_of_pos (sq_pos_of_pos hr))

variable [InnerProductSpace ℝ E]

theorem contDiff_movingBump_space (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) :
    ContDiff ℝ ∞ (movingBump rho C a gamma t) := by
  unfold movingBump ballGap
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))))

theorem contDiff_movingBump (rho C a : ℝ) {gamma : ℝ → E}
    (hg : ContDiff ℝ ∞ gamma) :
    ContDiff ℝ ∞ (fun z : ℝ × E => movingBump rho C a gamma z.1 z.2) := by
  unfold movingBump ballGap
  exact (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_fst.sub contDiff_const))).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub
      ((contDiff_norm_sq ℝ).comp (contDiff_snd.sub (hg.comp contDiff_fst)))))

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.Barrier
