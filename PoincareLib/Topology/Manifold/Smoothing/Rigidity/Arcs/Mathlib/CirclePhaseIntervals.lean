import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.Mathlib.CircleClosedArc
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Tactic.Linarith

/-!
# Separated actual phase intervals in one quotient period

Two distinct interior phases have disjoint larger real neighborhoods
inside the same injective quotient interval. The actual open quotient
arcs retain their complete real membership tests. See Waldhausen1968
section1.3 and rigidity056, sections1,3 and6.
-/

set_option autoImplicit false

open Set

namespace AddCircle

/-- The actual open quotient image of a specified real interval.
See rigidity056, section1. -/
def openIntervalArc (p a b : ℝ) : Set (AddCircle p) :=
  (fun t : ℝ => (t : AddCircle p)) '' Ioo a b

/-- The whole interval image is open in the circle, including when
the interval is empty. See rigidity056, section1. -/
theorem isOpen_openIntervalArc (p a b : ℝ) : IsOpen (openIntervalArc p a b) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- On one full injective period, membership in the actual open
arc is exactly the strict real interval test. See rigidity056,
sections1 and6. -/
theorem coe_mem_openIntervalArc_iff (p : ℝ) [Fact (0 < p)]
    {a b z : ℝ} (ha : 0 ≤ a) (hb : b ≤ p) (hz : z ∈ Ico 0 p) :
    (z : AddCircle p) ∈ openIntervalArc p a b ↔ z ∈ Ioo a b := by
  constructor
  · rintro ⟨t, ht, htz⟩
    have htI : t ∈ Ico (0 : ℝ) (0 + p) :=
      ⟨ha.trans ht.1.le, by simpa only [zero_add] using ht.2.trans_le hb⟩
    have hzI : z ∈ Ico (0 : ℝ) (0 + p) := by simpa only [zero_add] using hz
    have htz' : t = z := (coe_eq_coe_iff_of_mem_Ico htI hzI).mp htz
    exact htz' ▸ ht
  · exact fun h => ⟨z, h, rfl⟩

/-- Ordered disjoint real intervals in one period have disjoint
whole quotient images. See rigidity056, section1. -/
theorem disjoint_openIntervalArc_of_le (p : ℝ) [Fact (0 < p)]
    {a b c d : ℝ} (ha : 0 ≤ a) (hbc : b ≤ c) (hd : d ≤ p) :
    Disjoint (openIntervalArc p a b) (openIntervalArc p c d) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxI : x ∈ Ico (0 : ℝ) (0 + p) := by
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hyI : y ∈ Ico (0 : ℝ) (0 + p) := by
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hxy : x = y := (coe_eq_coe_iff_of_mem_Ico hxI hyI).mp (hxz.trans hyz.symm)
  linarith [hx.2, hy.1]

/-- A phase interval contained in the open period lies wholly in
the original quotient chart omitting zero. See rigidity056,
section3; no global real lift is asserted. -/
theorem openIntervalArc_subset_coe_chart (p : ℝ) [Fact (0 < p)]
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ p) :
    openIntervalArc p a b ⊆ (openPartialHomeomorphCoe p 0).target := by
  rintro z ⟨t, ht, rfl⟩
  apply (openPartialHomeomorphCoe p 0).map_source
  change t ∈ Ioo (0 : ℝ) (0 + p)
  exact ⟨ha.trans_lt ht.1, by simpa only [zero_add] using ht.2.trans_le hb⟩

/-- Actual distinct phases inside a period admit one positive
width whose double neighborhoods remain separated and inside that
period. See rigidity056, section1. -/
theorem exists_separated_phase_width {p a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < p) :
    ∃ eta : ℝ, 0 < eta ∧ 0 < a - 2 * eta ∧
      a + 2 * eta < b - 2 * eta ∧ b + 2 * eta < p := by
  let m := min a (min (b - a) (p - b))
  have hm : 0 < m := lt_min ha (lt_min (sub_pos.mpr hab) (sub_pos.mpr hb))
  have hma : m ≤ a := min_le_left _ _
  have hmab : m ≤ b - a := (min_le_right _ _).trans (min_le_left _ _)
  have hmb : m ≤ p - b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨m / 8, ?_, ?_, ?_, ?_⟩ <;> linarith

end AddCircle
