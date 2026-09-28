import PoincareConjecture.Proofs.M35.RadialGauge.PolynomialInterpolation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs










set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge



theorem polynomial_iteratedDeriv_bounds
    {α : Type*} {p : α → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (p a))
    (hjets : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ a r, 0 ≤ r →
      |iteratedDeriv j (p a) r| ≤ M)
    (hvalue : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r →
      (1 + r ^ 2) ^ n * |p a r| ≤ C) :
    ∀ j n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r →
      (1 + r ^ 2) ^ n * |iteratedDeriv j (p a) r| ≤ C := by
  have hsj (j : ℕ) (a : α) : ContDiff ℝ ∞ (iteratedDeriv j (p a)) := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using hs a
    | succ j ih =>
        rw [iteratedDeriv_succ]
        exact (contDiff_infty_iff_deriv.mp ih).2
  intro j
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hvalue
  | succ j ih =>
      intro n
      obtain ⟨C, hC, hvaluej⟩ := ih (n + n)
      obtain ⟨M, hM, hMj⟩ := hjets (j + 1 + 1)
      refine ⟨2 * C + M, by positivity, ?_⟩
      intro a r hr
      have hsecond (z : ℝ) (hz : 0 ≤ z) :
          |deriv (deriv (iteratedDeriv j (p a))) z| ≤ M := by
        simpa only [iteratedDeriv_succ] using hMj a z hz
      have h := polynomial_deriv_bound (hsj j a) n hM (hvaluej a) hsecond r hr
      simpa only [iteratedDeriv_succ] using h

end PoincareConjecture.M35.RadialGauge
