import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary chord-cone distance identities

The chord-cone formula has radial and link lower bounds and an annular
upper bound. Triangle is not asserted for arbitrary chord metrics.
Source: Morgan--Tian Proposition 10.29, pp. 262-263; M28 derivation 154.
-/

noncomputable section
set_option autoImplicit false

namespace PoincareMT.M28

/-- The cone distance formula in chord coordinates. A geometric triangle
law must be supplied separately. Source: M28 derivations 152 and 154. -/
def chordConeDistance (r s d : ℝ) : ℝ :=
  Real.sqrt ((r - s) ^ 2 + r * s * d ^ 2)

/-- The chord-cone formula is nonnegative. Derivation 154. -/
theorem chordConeDistance_nonneg (r s d : ℝ) : 0 ≤ chordConeDistance r s d :=
  Real.sqrt_nonneg _

/-- Squaring the formula is valid at nonnegative radii. Derivation 154. -/
theorem chordConeDistance_sq {r s d : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    chordConeDistance r s d ^ 2 = (r - s) ^ 2 + r * s * d ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hr hs) (sq_nonneg _)))

/-- Identical radius and direction have zero distance. Derivation 154. -/
theorem chordConeDistance_self (r : ℝ) : chordConeDistance r r 0 = 0 := by
  simp [chordConeDistance]

/-- Swapping the radii preserves the chord-cone formula. Derivation 154. -/
theorem chordConeDistance_comm (r s d : ℝ) :
    chordConeDistance r s d = chordConeDistance s r d := by
  unfold chordConeDistance
  congr 1
  ring

/-- Radius difference is bounded by cone distance at nonnegative radii.
This is the actual radius Lipschitz bound. Derivation 154. -/
theorem abs_sub_le_chordConeDistance {r s d : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |r - s| ≤ chordConeDistance r s d := by
  apply Real.abs_le_sqrt
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hr hs) (sq_nonneg d))

/-- On an annulus away from zero, cone distance controls link distance.
No upper bound on the chord is needed. Derivation 154. -/
theorem mul_le_chordConeDistance {a r s d : ℝ}
    (ha : 0 ≤ a) (hr : a ≤ r) (hs : a ≤ s) :
    a * d ≤ chordConeDistance r s d := by
  apply Real.le_sqrt_of_sq_le
  have hp : a * a ≤ r * s := mul_le_mul hr hs ha (ha.trans hr)
  have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg d)
  nlinarith only [hmul, sq_nonneg (r - s)]

/-- A finite outer radius bounds cone distance by radial plus link
distance. Derivation 154. -/
theorem chordConeDistance_le_abs_sub_add_mul {b r s d : ℝ}
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (hr : r ≤ b) (hs : s ≤ b) (hd : 0 ≤ d) :
    chordConeDistance r s d ≤ |r - s| + b * d := by
  have hb : 0 ≤ b := hr0.trans hr
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (abs_nonneg _) (mul_nonneg hb hd), ?_⟩
  have hp : r * s ≤ b * b := mul_le_mul hr hs hs0 hb
  have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg d)
  have hcross : 0 ≤ |r - s| * (b * d) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg hb hd)
  nlinarith only [hmul, hcross, sq_abs (r - s)]

/-- The literal radial dilation satisfies the simultaneous potential
law used on a finite cone annulus. Derivation 154. -/
theorem chordConeDistance_dilation_sq {r s d c : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hc : 0 ≤ c) :
    chordConeDistance r (c * s) d ^ 2 =
      c ^ 2 * s ^ 2 + r ^ 2 -
        c * (s ^ 2 + r ^ 2 - chordConeDistance r s d ^ 2) := by
  rw [chordConeDistance_sq hr (mul_nonneg hc hs), chordConeDistance_sq hr hs]
  ring

end PoincareMT.M28
