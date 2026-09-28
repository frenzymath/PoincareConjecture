import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul










set_option autoImplicit false

open Filter
open scoped ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]




theorem secondDeriv_comp_of_contDiffAt_two (f : E → W) (y : ℝ → E) (s : ℝ)
    (hf : ContDiffAt ℝ 2 f (y s)) (hy : ContDiffAt ℝ 2 y s) :
    deriv (deriv (fun t => f (y t))) s =
      fderiv ℝ (fderiv ℝ f) (y s) (deriv y s) (deriv y s) +
        fderiv ℝ f (y s) (deriv (deriv y) s) := by
  have hfy : ∀ᶠ x in 𝓝 (y s), DifferentiableAt ℝ f x :=
    ((hf.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by simp)).mono
      (fun x hx => hx.differentiableAt (by simp))
  have hyt : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ y t :=
    ((hy.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by simp)).mono
      (fun t ht => ht.differentiableAt (by simp))
  have hfirst : deriv (fun t => f (y t)) =ᶠ[𝓝 s]
      (fun t => fderiv ℝ f (y t) (deriv y t)) := by
    filter_upwards [hy.continuousAt.tendsto.eventually hfy, hyt] with t hft hyt'
    exact (hft.hasFDerivAt.comp_hasDerivAt t hyt'.hasDerivAt).deriv
  have hd := (hy.differentiableAt (by norm_num)).hasDerivAt
  have hdf := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by simp)).hasFDerivAt
  have hdy := ((hy.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by simp)).hasDerivAt
  have hsecond := (hdf.comp_hasDerivAt s hd).clm_apply hdy
  rw [hfirst.deriv_eq]
  exact hsecond.deriv

end PoincareConjecture.M63
