import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.ChordConeDistance

/-!
# Positive homogeneity of the actual chord-cone distance

The same factor rescales both tested radii and the resulting distance.
Source: Morgan--Tian Proposition 10.29, pp. 262-263; derivation 158.
-/

noncomputable section
set_option autoImplicit false

namespace PoincareMT.M28

/-- A nonnegative common radial factor multiplies the chord-cone
distance by that same factor. Source: Proposition 10.29; derivation 158. -/
theorem chordConeDistance_mul (h : ℝ) (hh : 0 ≤ h) (r s d : ℝ) :
    chordConeDistance (h * r) (h * s) d = h * chordConeDistance r s d := by
  unfold chordConeDistance
  have hid : (h * r - h * s) ^ 2 + (h * r) * (h * s) * d ^ 2 =
      h ^ 2 * ((r - s) ^ 2 + r * s * d ^ 2) := by ring
  rw [hid, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh]

end PoincareMT.M28
