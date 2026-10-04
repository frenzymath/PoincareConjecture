import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Difference norms under the spatial jet identifications

The standard currying isometries preserve differences as well as norms.
These identities apply to totalized derivatives and require no extra
regularity. They are used for the C2 collar modulus in Morgan--Tian,
Lemma 16.8, pp. 372-373; see M44 derivation 41.
-/

set_option autoImplicit false

namespace PoincareMT.M44

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The zeroth spatial jet preserves difference norms. Source:
the coordinate C2 comparison in Lemma 16.8; M44 derivation 41. -/
theorem norm_iteratedFDeriv_zero_sub (f g : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g x‖ = ‖f x - g x‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- Currying the last derivative slot preserves difference norms.
Source: the coordinate C2 comparison in Lemma 16.8; M44 derivation 41. -/
theorem norm_iteratedFDeriv_fderiv_sub (m : ℕ) (f g : E → F) (x : E) :
    ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ g) x‖ =
      ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) g x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  let L := (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
  change ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ g) x‖ =
    ‖L (iteratedFDeriv ℝ m (fderiv ℝ f) x) - L (iteratedFDeriv ℝ m (fderiv ℝ g) x)‖
  rw [← L.map_sub, L.norm_map]

/-- The first derivative and first spatial jet have the same
difference norm. Source: Lemma 16.8; M44 derivation 41. -/
theorem norm_fderiv_sub_eq_jet (f g : E → F) (x : E) :
    ‖fderiv ℝ f x - fderiv ℝ g x‖ =
      ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ := by
  rw [← norm_iteratedFDeriv_zero_sub (fderiv ℝ f) (fderiv ℝ g) x,
    norm_iteratedFDeriv_fderiv_sub]

end PoincareMT.M44
