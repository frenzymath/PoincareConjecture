import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv










set_option autoImplicit false

open scoped intervalIntegral

namespace Function.Periodic



theorem integral_deriv_smul_comp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℝ} (hper : Function.Periodic f p) (hf : Continuous f)
    {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi)
    (hshift : ∀ x, phi (x + p) = phi x + p) (q : ℝ) :
    (∫ x in q..q + p, deriv phi x • f (phi x)) = ∫ x in (0 : ℝ)..p, f x := by
  calc
    _ = ∫ x in phi q..phi (q + p), f x :=
      intervalIntegral.integral_deriv_smul_comp
        (fun x _ => (hphi.differentiable (by norm_num) x).hasDerivAt)
        hphi.continuous_deriv_one.continuousOn hf
    _ = _ := by
      rw [hshift q]
      simpa only [zero_add] using hper.intervalIntegral_add_eq (phi q) 0

end Function.Periodic
