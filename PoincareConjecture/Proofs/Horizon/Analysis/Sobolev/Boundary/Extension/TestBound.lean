import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2








set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace Poincare.Analysis.Sobolev.BoundaryExtension

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_norm_le_normalCoord {ψ : E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hface : ∀ x : E, x 0 = 0 → ψ x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, 0 ≤ x 0 → ‖ψ x‖ ≤ C * x 0 := by
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hψ.continuous_fderiv (by simp))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  let y : E := x - x 0 • EuclideanSpace.single 0 1
  have hy : y 0 = 0 := by simp [y]
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (univ : Set E)) => hψ.differentiable (by simp) z)
    (fun z (_ : z ∈ (univ : Set E)) => (hC z).trans (le_max_left C 0))
    (convex_univ : Convex ℝ (univ : Set E)) (mem_univ y) (mem_univ x)
  rw [hface y hy, sub_zero] at hmv
  simpa [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx] using hmv

end Poincare.Analysis.Sobolev.BoundaryExtension
