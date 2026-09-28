import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring









noncomputable section
set_option autoImplicit false

namespace PoincareConjecture.M28



def chordConeDistance (r s d : ℝ) : ℝ :=
  Real.sqrt ((r - s) ^ 2 + r * s * d ^ 2)


theorem chordConeDistance_nonneg (r s d : ℝ) : 0 ≤ chordConeDistance r s d :=
  Real.sqrt_nonneg _


theorem chordConeDistance_sq {r s d : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    chordConeDistance r s d ^ 2 = (r - s) ^ 2 + r * s * d ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hr hs) (sq_nonneg _)))


theorem chordConeDistance_self (r : ℝ) : chordConeDistance r r 0 = 0 := by
  simp [chordConeDistance]


theorem chordConeDistance_comm (r s d : ℝ) :
    chordConeDistance r s d = chordConeDistance s r d := by
  unfold chordConeDistance
  congr 1
  ring



theorem abs_sub_le_chordConeDistance {r s d : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |r - s| ≤ chordConeDistance r s d := by
  apply Real.abs_le_sqrt
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hr hs) (sq_nonneg d))



theorem mul_le_chordConeDistance {a r s d : ℝ}
    (ha : 0 ≤ a) (hr : a ≤ r) (hs : a ≤ s) :
    a * d ≤ chordConeDistance r s d := by
  apply Real.le_sqrt_of_sq_le
  have hp : a * a ≤ r * s := mul_le_mul hr hs ha (ha.trans hr)
  have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg d)
  nlinarith only [hmul, sq_nonneg (r - s)]



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



theorem chordConeDistance_dilation_sq {r s d c : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hc : 0 ≤ c) :
    chordConeDistance r (c * s) d ^ 2 =
      c ^ 2 * s ^ 2 + r ^ 2 -
        c * (s ^ 2 + r ^ 2 - chordConeDistance r s d ^ 2) := by
  rw [chordConeDistance_sq hr (mul_nonneg hc hs), chordConeDistance_sq hr hs]
  ring

end PoincareConjecture.M28
