import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace AddCircle

def openIntervalArc (p a b : ℝ) : Set (AddCircle p) :=
  (fun t : ℝ => (t : AddCircle p)) '' Ioo a b

theorem isOpen_openIntervalArc (p a b : ℝ) : IsOpen (openIntervalArc p a b) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

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

theorem openIntervalArc_subset_coe_chart (p : ℝ) [Fact (0 < p)]
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ p) :
    openIntervalArc p a b ⊆ (openPartialHomeomorphCoe p 0).target := by
  rintro z ⟨t, ht, rfl⟩
  apply (openPartialHomeomorphCoe p 0).map_source
  change t ∈ Ioo (0 : ℝ) (0 + p)
  exact ⟨ha.trans_lt ht.1, by simpa only [zero_add] using ht.2.trans_le hb⟩

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
