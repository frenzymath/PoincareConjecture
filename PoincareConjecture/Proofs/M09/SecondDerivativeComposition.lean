import PoincareConjecture.Proofs.M09.LocalMinimumHessian
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem secondDeriv_comp (f : E → ℝ) (y : ℝ → E) (s : ℝ)
    (hf : ContDiffAt ℝ ∞ f (y s)) (hy : ContDiffAt ℝ ∞ y s) :
    deriv (deriv (fun t ↦ f (y t))) s =
      fderiv ℝ (fderiv ℝ f) (y s) (deriv y s) (deriv y s) +
        fderiv ℝ f (y s) (deriv (deriv y) s) := by
  have hfy : ∀ᶠ x in 𝓝 (y s), DifferentiableAt ℝ f x :=
    ((hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun x hx ↦ hx.differentiableAt (by simp))
  have hyt : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ y t :=
    ((hy.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun t ht ↦ ht.differentiableAt (by simp))
  have hfirst : deriv (fun t ↦ f (y t)) =ᶠ[𝓝 s]
      (fun t ↦ fderiv ℝ f (y t) (deriv y t)) := by
    filter_upwards [hy.continuousAt.tendsto.eventually hfy, hyt] with t hft hyt'
    exact (hft.hasFDerivAt.comp_hasDerivAt t hyt'.hasDerivAt).deriv
  have hd := (hy.differentiableAt (by simp)).hasDerivAt
  have hdf := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hdy := ((hy.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hsecond := (hdf.comp_hasDerivAt s hd).clm_apply hdy
  rw [hfirst.deriv_eq]
  exact hsecond.deriv

end PoincareConjecture.Proofs.M09
