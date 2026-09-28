import PoincareConjecture.Proofs.M28.Mathlib.ChordConeDistance

noncomputable section
set_option autoImplicit false

namespace PoincareConjecture.M28

theorem chordConeDistance_mul (h : ℝ) (hh : 0 ≤ h) (r s d : ℝ) :
    chordConeDistance (h * r) (h * s) d = h * chordConeDistance r s d := by
  unfold chordConeDistance
  have hid : (h * r - h * s) ^ 2 + (h * r) * (h * s) * d ^ 2 =
      h ^ 2 * ((r - s) ^ 2 + r * s * d ^ 2) := by ring
  rw [hid, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh]

end PoincareConjecture.M28
