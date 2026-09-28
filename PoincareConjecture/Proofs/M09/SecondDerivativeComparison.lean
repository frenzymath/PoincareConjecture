import PoincareConjecture.Proofs.M09.SecondDerivativeComposition

set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

theorem localMin_secondDeriv_scaled_comparison (f g : ℝ → ℝ) (c x : ℝ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hmin : IsLocalMin (fun t ↦ f t - c * g t) x) :
    c * deriv (deriv g) x ≤ deriv (deriv f) x := by
  have hfn : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t :=
    ((hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun t ht ↦ ht.differentiableAt (by simp))
  have hgn : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ g t :=
    ((hg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun t ht ↦ ht.differentiableAt (by simp))
  have hfirst : deriv (fun t ↦ f t - c * g t) =ᶠ[𝓝 x]
      (fun t ↦ deriv f t - c * deriv g t) := by
    filter_upwards [hfn, hgn] with t hft hgt
    exact (hft.hasDerivAt.sub (hgt.hasDerivAt.const_mul c)).deriv
  have hdf := ((hf.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hdg := ((hg.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hsecond : deriv (fun t ↦ deriv f t - c * deriv g t) x =
      deriv (deriv f) x - c * deriv (deriv g) x := (hdf.sub (hdg.const_mul c)).deriv
  have hpos := localMin_secondDeriv_nonneg (fun t ↦ f t - c * g t) x
    (hf.continuousAt.sub (continuousAt_const.mul hg.continuousAt)) hmin
  rw [hfirst.deriv_eq, hsecond] at hpos
  exact sub_nonneg.mp hpos

end PoincareConjecture.Proofs.M09
