import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLArithmetic

/-!
# Minimum of two finite PL scalar maps

The minimum is the first map minus the positive part of their
difference. The existing common-refinement and zero-hyperplane
constructions retain the exact finite carrier. See Hudson
pp. 15--19 and the square-shell construction in M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The pointwise minimum of two finite PL scalar maps is
finite PL on their common exact source. See Hudson pp. 15--19
and M76 derivation 270. -/
theorem FinitePiecewiseAffineOn.min {f g : E → ℝ} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => min (f x) (g x)) S := by
  apply (hf.sub (hf.sub hg).positivePart).congr
  intro x _
  change f x - max 0 (f x - g x) = Min.min (f x) (g x)
  by_cases h : f x ≤ g x
  · rw [min_eq_left h, max_eq_left (by linarith), sub_zero]
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (by linarith)]
    ring

end Geometry
