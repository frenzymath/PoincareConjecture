import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Change of variable over a single period

The ordinary substitution theorem and phase invariance of periodic integrals
give the change of parameter used for geometric integrals in MT2007
Lemma 19.6, pp. 441-442, and the M63 contract review, block 8.
The abstract oriented identity needs no monotonicity or inverse map.
-/

set_option autoImplicit false

open scoped intervalIntegral

namespace Function.Periodic

/-- A C1 label map preserving one period transports the integral with its
signed Jacobian. This is the periodic substitution used in MT2007 p. 441. -/
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
