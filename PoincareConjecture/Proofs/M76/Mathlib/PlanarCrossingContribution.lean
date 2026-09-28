import PoincareConjecture.Proofs.M76.Mathlib.PlanarSegmentHeight
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PlanarSegment

noncomputable def horizontalStep (a : ℝ) (q : ℝ × ℝ) : ℤ :=
  if a ≤ q.1 then 1 else 0

noncomputable def aboveLine (a b q : ℝ × ℝ) : ℤ :=
  if q.2 < height a b q.1 then 1 else 0

noncomputable def crossingContribution (a b q : ℝ × ℝ) : ℤ :=
  (horizontalStep a.1 q - horizontalStep b.1 q) * aboveLine a b q

theorem eventuallyEq_horizontalStep {a : ℝ} {q : ℝ × ℝ} (h : q.1 ≠ a) :
    ∀ᶠ z in 𝓝 q, horizontalStep a z = horizontalStep a q := by
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [continuous_fst.continuousAt.eventually_lt_const h] with z hz
    simp [horizontalStep, not_le_of_gt h, not_le_of_gt hz]
  · filter_upwards [continuous_fst.continuousAt.eventually_const_lt h] with z hz
    simp [horizontalStep, h.le, hz.le]

theorem eventuallyEq_aboveLine {a b q : ℝ × ℝ} (h : q.2 ≠ height a b q.1) :
    ∀ᶠ z in 𝓝 q, aboveLine a b z = aboveLine a b q := by
  have hc := ((continuous_height a b).comp continuous_fst).continuousAt (x := q)
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [continuous_snd.continuousAt.eventually_lt hc h] with z hz
    change z.2 < height a b z.1 at hz
    simp [aboveLine, h, hz]
  · filter_upwards [hc.eventually_lt continuous_snd.continuousAt h] with z hz
    change height a b z.1 < z.2 at hz
    simp [aboveLine, not_lt_of_ge h.le, not_lt_of_ge hz.le]

theorem eventually_crossingContribution {a b q : ℝ × ℝ}
    (hab : a.1 ≠ b.1) (hq : q ∉ segment ℝ a b) :
    ∀ᶠ z in 𝓝 q, crossingContribution a b z =
      (horizontalStep a.1 z - horizontalStep b.1 z) * aboveLine a b q := by
  by_cases heq : q.2 = height a b q.1
  · have hx : q.1 ∉ uIcc a.1 b.1 :=
      fun h => hq ((mem_segment_iff hab).mpr ⟨h, heq⟩)
    have hout : q.1 < min a.1 b.1 ∨ max a.1 b.1 < q.1 := by
      simpa only [uIcc, mem_Icc, not_and_or, not_le] using hx
    rcases hout with h | h
    · filter_upwards [continuous_fst.continuousAt.eventually_lt_const h] with z hz
      have ha := hz.trans_le (min_le_left _ _)
      have hb := hz.trans_le (min_le_right _ _)
      simp [crossingContribution, horizontalStep, not_le_of_gt ha, not_le_of_gt hb]
    · filter_upwards [continuous_fst.continuousAt.eventually_const_lt h] with z hz
      have ha := (le_max_left _ _).trans hz.le
      have hb := (le_max_right _ _).trans hz.le
      simp [crossingContribution, horizontalStep, ha, hb]
  · filter_upwards [eventuallyEq_aboveLine heq] with z hz
    simp only [crossingContribution, hz]

end PlanarSegment
