import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.OrbitMargins
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal

namespace PoincareConjecture

def packingMass (n : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n.factorial : ℝ) * (3 / 2 : ℝ) ^ n) *
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)

theorem packingMass_ne_top (n : ℕ) (s : ℝ) : packingMass n s ≠ ∞ := by
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top

def packingCount (n : ℕ) (s w : ℝ) : ℕ :=
  ⌈(packingMass n s).toReal / w⌉₊ + 1

theorem packingCount_pos (n : ℕ) (s w : ℝ) : 0 < packingCount n s w := by
  unfold packingCount
  omega

theorem packingMass_lt_count_mul_volume (n : ℕ) (s : ℝ) {w : ℝ} (hw : 0 < w) :
    packingMass n s < ((packingCount n s w + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal w := by
  have hceil := Nat.le_ceil ((packingMass n s).toReal / w)
  have hcount : (packingMass n s).toReal / w < (packingCount n s w + 1 : ℕ) := by
    unfold packingCount
    push_cast
    linarith
  have hreal : (packingMass n s).toReal < ((packingCount n s w + 1 : ℕ) : ℝ) * w :=
    (div_lt_iff₀ hw).mp hcount
  apply (ENNReal.toReal_lt_toReal (packingMass_ne_top n s)
    (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hw.le] using hreal

def packingInjectivityRadius (n : ℕ) (s w : ℝ) : ℝ :=
  min (s / 8) (loopPowerThreshold s (packingCount n s w) / 2)

theorem packingInjectivityRadius_pos (n : ℕ) {s : ℝ} (hs : 0 < s) (w : ℝ) :
    0 < packingInjectivityRadius n s w := by
  unfold packingInjectivityRadius
  exact lt_min (by positivity) (div_pos (loopPowerThreshold_pos hs _) (by norm_num))

theorem packingInjectivityRadius_lt (n : ℕ) {s : ℝ} (hs : 0 < s) (w : ℝ) :
    packingInjectivityRadius n s w < s := by
  have h := min_le_left (s / 8) (loopPowerThreshold s (packingCount n s w) / 2)
  change packingInjectivityRadius n s w ≤ s / 8 at h
  linarith

theorem twice_packingInjectivityRadius_lt (n : ℕ) {s : ℝ} (hs : 0 < s) (w : ℝ) :
    2 * packingInjectivityRadius n s w < s := by
  have h := min_le_left (s / 8) (loopPowerThreshold s (packingCount n s w) / 2)
  change packingInjectivityRadius n s w ≤ s / 8 at h
  linarith

theorem twice_packingInjectivityRadius_le_loopPowerThreshold (n : ℕ) (s w : ℝ) :
    2 * packingInjectivityRadius n s w ≤ loopPowerThreshold s (packingCount n s w) := by
  have h := min_le_right (s / 8) (loopPowerThreshold s (packingCount n s w) / 2)
  change packingInjectivityRadius n s w ≤ loopPowerThreshold s (packingCount n s w) / 2 at h
  linarith

theorem norm_two_smul_le_loopPowerThreshold
    (n : ℕ) {s w : ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ ≤ packingInjectivityRadius n s w) :
    ‖(2 : ℝ) • v‖ ≤ loopPowerThreshold s (packingCount n s w) := by
  have h := twice_packingInjectivityRadius_le_loopPowerThreshold n s w
  rw [norm_smul]
  norm_num
  linarith

theorem loop_endpoint_center_lift_margin
    {E : Type*} [NormedAddCommGroup E] {s ell : ℝ}
    (hs : 0 < s) (hell : 0 ≤ ell) (N : ℕ)
    (hshort : ell ≤ loopPowerThreshold s N)
    (i : ℕ) (hi : i ≤ N) (y : E) (hy : ‖y‖ ≤ 2 * (i : ℝ) * ell) :
    ‖y‖ + 2 * (s / 4) < s := by
  have hmargin := (loopPowerThreshold_margins hs hell N hshort).1
  have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hmul := mul_le_mul_of_nonneg_right hi' hell
  nlinarith

end PoincareConjecture
