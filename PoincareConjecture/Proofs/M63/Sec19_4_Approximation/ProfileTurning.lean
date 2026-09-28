import PoincareConjecture.Proofs.M63.Mathlib.ScalarTurningIntegral
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.Profile
import Mathlib.Analysis.Calculus.Deriv.Shift










set_option autoImplicit false

open Set
open scoped ContDiff intervalIntegral

namespace PoincareConjecture



theorem m63Profile_turning_integral_le_pi {N : ℕ} (hN : 0 < N) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (t : ℝ) :
    (∫ x in t..(t + m63CellLength N),
      A * B * |deriv (m63Profile N) x| / (A ^ 2 * m63Profile N x ^ 2 + B ^ 2)) ≤
      Real.pi := by
  have hperiod := m63Profile_periodic hN
  have hfun : (fun x => m63Profile N (x + m63CellLength N)) = m63Profile N :=
    funext hperiod
  have hdperiod : Function.Periodic (deriv (m63Profile N)) (m63CellLength N) := by
    intro x
    rw [← deriv_comp_add_const, hfun]
  have hdensity : Function.Periodic
      (fun x => A * B * |deriv (m63Profile N) x| /
        (A ^ 2 * m63Profile N x ^ 2 + B ^ 2)) (m63CellLength N) := by
    intro x
    dsimp only
    rw [hperiod x, hdperiod x]
  rw [hdensity.intervalIntegral_add_eq t 0, zero_add]
  apply intervalIntegral.integral_turningDensity_le_pi
    ((m63Profile_smooth N).of_le (by simp)) (m63CellLength_pos hN) hA hB
  · simpa using m63Profile_flat hN 0 0
  · exact fun x _ => m63Profile_symmetric hN x
  · exact m63Profile_monotone_half hN

end PoincareConjecture
