import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Radial normalization and its tangential derivative

These calculus facts support the intrinsic C1 loop contraction in
Morgan--Tian Lemma 18.27, printed p. 434. The derivation and the behavior
of the total function at zero are recorded in the task's radial-extension note.
-/

set_option autoImplicit false

open scoped ContDiff RealInnerProductSpace

namespace PoincareMT.LoopSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Radial normalization, used to restrict a C1 extension to circle values
in MT Lemma 18.27, p. 434. Smoothness will only be used away from zero. -/
noncomputable def radialNormalization (x : E) : E := ‖x‖⁻¹ • x

/-- The normalized nonzero vector is a unit vector. Source: the radial
extension calculation for MT Lemma 18.27, p. 434. -/
theorem norm_radialNormalization {x : E} (hx : x ≠ 0) :
    ‖radialNormalization x‖ = 1 := by
  simp [radialNormalization, norm_smul, norm_inv, norm_ne_zero_iff.mpr hx]

/-- Normalization fixes the unit sphere. Source: the radial extension
calculation for MT Lemma 18.27, p. 434. -/
theorem radialNormalization_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    radialNormalization x = x := by
  simp [radialNormalization, hx]

/-- Radial normalization is smooth at each nonzero point. Source: the
radial extension calculation for MT Lemma 18.27, p. 434. -/
theorem contDiffAt_radialNormalization {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ radialNormalization x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

/-- On the unit sphere, normalization preserves orthogonal tangent vectors.
Source: the radial extension calculation for MT Lemma 18.27, p. 434. -/
theorem fderiv_radialNormalization_tangent {x v : E}
    (hx : ‖x‖ = 1) (hv : ⟪x, v⟫ = 0) :
    fderiv ℝ radialNormalization x v = v := by
  have hnorm : HasFDerivAt (fun y : E => ‖y‖) (innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by rw [hx]; norm_num)
    simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
    convert h using 1
    ext y
    simp [hx]
  have hinv := (hasDerivAt_inv (by rw [hx]; exact one_ne_zero)).comp_hasFDerivAt x hnorm
  have hrad : HasFDerivAt (fun y : E => ‖y‖⁻¹ • y) _ x :=
    hinv.smul (hasFDerivAt_id x)
  change fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x v = v
  rw [hrad.fderiv]
  simp [hx, hv]

end PoincareMT.LoopSpace
