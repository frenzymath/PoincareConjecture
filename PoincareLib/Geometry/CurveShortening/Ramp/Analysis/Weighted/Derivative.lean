import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.MaximumPrinciple
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Product and quotient rules for an iterated weighted derivative

These scalar identities retain the derivative of the variable weight in the
arc-length calculation of corrected Lemma 19.14, MT2007 p. 447 and
MT2015Correction pp. 8-9. See the checked derivation
`proof-work/tasks/M63/derivations/2026-09-21-smooth-ratio-estimate.md`.
-/

set_option autoImplicit false

namespace Poincare.Parabolic

/-- Twice applying `w * deriv` obeys the second product rule, including for
a variable weight. This is the spatial calculation for corrected Lemma 19.14,
MT2015Correction pp. 8-9. -/
theorem weighted_second_mul {f g w : ℝ → ℝ} {x : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hw : DifferentiableAt ℝ w x) :
    w x * deriv (fun y => w y * deriv (fun z => f z * g z) y) x =
      f x * (w x * deriv (fun y => w y * deriv g y) x) +
        2 * (w x * deriv f x) * (w x * deriv g x) +
        g x * (w x * deriv (fun y => w y * deriv f y) x) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hfirst : deriv (fun y => f y * g y) =
      fun y => deriv f y * g y + f y * deriv g y := by
    funext y
    exact deriv_fun_mul (hfd y) (hgd y)
  have hsecond : deriv (deriv (fun y => f y * g y)) x =
      (deriv (deriv f) x * g x + deriv f x * deriv g x) +
        (deriv f x * deriv g x + f x * deriv (deriv g) x) := by
    rw [hfirst]
    exact (((hf.differentiable_deriv_two x).hasDerivAt.mul
      (hgd x).hasDerivAt).add ((hfd x).hasDerivAt.mul
        (hg.differentiable_deriv_two x).hasDerivAt)).deriv
  rw [weighted_deriv_eq hw ((hf.mul hg).differentiable_deriv_two x),
    weighted_deriv_eq hw (hg.differentiable_deriv_two x),
    weighted_deriv_eq hw (hf.differentiable_deriv_two x), hsecond, hfirst]
  ring

/-- The spatial quotient identity for the actual iterated weighted derivative.
The nonzero denominator and twice differentiable slices justify every product
and quotient rule in corrected Lemma 19.14, MT2015Correction pp. 8-9. -/
theorem weighted_second_div {f g w : ℝ → ℝ} {x : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hne : ∀ y, g y ≠ 0) (hw : DifferentiableAt ℝ w x) :
    (w x * deriv (fun y => w y * deriv f y) x) / g x -
        f x * (w x * deriv (fun y => w y * deriv g y) x) / g x ^ 2 =
      w x * deriv (fun y => w y * deriv (fun z => f z / g z) y) x +
        2 * (w x * deriv g x) / g x * (w x * deriv (fun y => f y / g y) x) := by
  have hq : ContDiff ℝ 2 (fun y => f y / g y) := hf.div hg hne
  have hcancel : (fun y => (f y / g y) * g y) = f :=
    funext (fun y => div_mul_cancel₀ _ (hne y))
  have h := weighted_second_mul hq hg hw
  rw [hcancel] at h
  field_simp [hne x] at h ⊢
  nlinarith [h]

end Poincare.Parabolic
