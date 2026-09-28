import PoincareConjecture.Proofs.M03.Existence.EuclideanTranslationNative
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv











set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture




theorem m65C1L2_testDerivative {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfL2 : MemLp f 2 volume) (v : EuclideanSpace ℝ (Fin d))
    (hdL2 : MemLp (fun x => fderiv ℝ f x v) 2 volume)
    (test : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    ⟪hdL2.toLp (fun x => fderiv ℝ f x v), test.toLp 2 volume⟫_ℝ =
      -⟪hfL2.toLp f, (∂_{v} test).toLp 2 volume⟫_ℝ := by
  have htestD : MemLp (fun x => fderiv ℝ test x v) 2 volume :=
    (∂_{v} test).memLp 2 volume
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hdL2.integrable_mul (test.memLp 2 volume))
    (hfL2.integrable_mul htestD) (hfL2.integrable_mul (test.memLp 2 volume))
    (fun x _ => (hf.differentiable (by decide)) x) (fun x _ => test.differentiableAt (x := x))
  have hleft : ⟪hdL2.toLp (fun x => fderiv ℝ f x v), test.toLp 2 volume⟫_ℝ =
      ∫ x, fderiv ℝ f x v * test x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hdL2.coeFn_toLp, test.coeFn_toLp 2 volume] with x hx htest
    simp only [hx, htest, Real.inner_apply]
  have hright : ⟪hfL2.toLp f, (∂_{v} test).toLp 2 volume⟫_ℝ =
      ∫ x, f x * fderiv ℝ test x v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfL2.coeFn_toLp, (∂_{v} test).coeFn_toLp 2 volume] with x hx htest
    simp only [hx, htest, SchwartzMap.lineDerivOp_apply_eq_fderiv, Real.inner_apply]
  rw [hleft, hright]
  linarith only [hibp]

end PoincareConjecture
