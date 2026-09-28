import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

namespace PoincareConjecture.M60

theorem exists_contDiffAt_angle {z : ℂ} (hz : z ≠ 0) :
    ∃ theta : ℂ → ℝ, ContDiffAt ℝ 1 theta z ∧
      ∀ w : ℂ, (‖w‖ : ℂ) * Complex.exp (theta w * Complex.I) = w := by
  let theta : ℂ → ℝ := fun w => z.arg + (Complex.log (w / z)).im
  refine ⟨theta, ?_, ?_⟩
  · have hlog : ContDiffAt ℝ 1 Complex.log (z / z) := by
      rw [div_self hz]
      exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
    have hdiv : ContDiff ℝ 1 (fun w : ℂ => w / z) := by
      simp only [div_eq_mul_inv]
      fun_prop
    exact contDiffAt_const.add
      (Complex.imCLM.contDiff.contDiffAt.comp z
        (hlog.comp z (f := fun w : ℂ => w / z) hdiv.contDiffAt))
  · intro w
    have hn : (‖w‖ : ℂ) = (‖z‖ : ℂ) * (‖w / z‖ : ℂ) := by
      rw [← Complex.ofReal_mul, ← norm_mul]
      congr 1
      field_simp
    dsimp only [theta]
    rw [Complex.log_im, Complex.ofReal_add, add_mul, Complex.exp_add, hn]
    calc
      _ = ((‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)) *
          ((‖w / z‖ : ℂ) * Complex.exp ((w / z).arg * Complex.I)) := by ring
      _ = z * (w / z) := by rw [Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I]
      _ = w := by field_simp

end PoincareConjecture.M60
