import PoincareConjecture.Proofs.Horizon.Topology.Maps.Homeomorph.CompactSupport
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

noncomputable section

set_option autoImplicit false

open Set

namespace Homeomorph.Vertical

def tent (r t : ℝ) : ℝ := max 0 (r - |t|)

theorem continuous_tent (r : ℝ) : Continuous (tent r) := by
  unfold tent
  fun_prop

theorem tent_eq_zero {r t : ℝ} (h : r ≤ |t|) : tent r t = 0 := by
  exact max_eq_left (sub_nonpos.mpr h)

theorem tent_lipschitz (r : ℝ) : LipschitzWith 1 (tent r) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  calc
    |tent r a - tent r b| ≤ max |(0 : ℝ) - 0| |(r - |a|) - (r - |b|)| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = |(|a| - |b|)| := by simp [abs_sub_comm, sub_sub_sub_cancel_left]
    _ ≤ |a - b| := abs_abs_sub_abs_le_abs_sub a b

def move (r h t : ℝ) : ℝ := t + h / r * tent r t

theorem continuous_move {X : Type*} [TopologicalSpace X]
    {r : ℝ} {h t : X → ℝ} (hh : Continuous h) (ht : Continuous t) :
    Continuous (fun x => move r (h x) (t x)) := by
  exact ht.add ((hh.div_const r).mul ((continuous_tent r).comp ht))

theorem move_eq_self {r h t : ℝ} (ht : r ≤ |t|) : move r h t = t := by
  simp [move, tent_eq_zero ht]

@[simp] theorem move_zero {r : ℝ} (hr : 0 < r) (h : ℝ) : move r h 0 = h := by
  simp [move, tent, max_eq_right hr.le, ne_of_gt hr]

theorem strictMono_move {r h : ℝ} (hr : 0 < r) (hh : |h| < r) :
    StrictMono (move r h) := by
  intro a b hab
  have hc : |h / r| < 1 := by
    rw [abs_div, abs_of_pos hr, div_lt_one hr]
    exact hh
  have hd : |tent r b - tent r a| ≤ b - a := by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_pos (sub_pos.mpr hab)]
      using (tent_lipschitz r).dist_le_mul b a
  have hmul : |h / r * (tent r b - tent r a)| < b - a := by
    rw [abs_mul]
    calc
      |h / r| * |tent r b - tent r a| ≤ |h / r| * (b - a) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ < 1 * (b - a) := mul_lt_mul_of_pos_right hc (sub_pos.mpr hab)
      _ = b - a := one_mul _
  have := (abs_lt.mp hmul).1
  dsimp [move]
  nlinarith

theorem surjective_move {r h : ℝ} : Function.Surjective (move r h) := by
  intro y
  let a := min (-|r|) y
  let b := max |r| y
  have ha : r ≤ |a| := by
    have ha' : a ≤ -|r| := min_le_left _ _
    have := neg_le_abs a
    have := le_abs_self r
    linarith
  have hb : r ≤ |b| := (le_abs_self r).trans ((le_max_left _ _).trans (le_abs_self b))
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  have hy : y ∈ Icc (move r h a) (move r h b) := by
    rw [move_eq_self ha, move_eq_self hb]
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab
    (continuous_move continuous_const continuous_id).continuousOn hy
  exact ⟨t, ht⟩

variable {X : Type*} [TopologicalSpace X]

def graphMap (r : ℝ) (h : X → ℝ) (z : X × ℝ) : X × ℝ :=
  (z.1, move r (h z.1) z.2)

theorem continuous_graphMap {r : ℝ} {h : X → ℝ} (hh : Continuous h) :
    Continuous (graphMap r h) :=
  continuous_fst.prodMk (continuous_move (hh.comp continuous_fst) continuous_snd)

omit [TopologicalSpace X] in
theorem bijective_graphMap {r : ℝ} {h : X → ℝ} (hr : 0 < r)
    (hh : ∀ x, |h x| < r) : Function.Bijective (graphMap r h) := by
  constructor
  · rintro ⟨x, t⟩ ⟨y, s⟩ heq
    have hxy : x = y := congrArg Prod.fst heq
    subst y
    have hts := (strictMono_move hr (hh x)).injective (congrArg Prod.snd heq)
    exact Prod.ext rfl hts
  · rintro ⟨x, t⟩
    obtain ⟨s, hs⟩ := surjective_move (r := r) (h := h x) t
    exact ⟨(x, s), Prod.ext rfl hs⟩

omit [TopologicalSpace X] in
theorem graphMap_eq_self {r : ℝ} {h : X → ℝ} {z : X × ℝ}
    (hz : r ≤ |z.2|) : graphMap r h z = z :=
  Prod.ext rfl (move_eq_self hz)

def graphHomeomorph [CompactSpace X] [T2Space X] {r : ℝ}
    (hr : 0 < r) (h : X → ℝ) (hh : Continuous h) (hbound : ∀ x, |h x| < r) :
    (X × ℝ) ≃ₜ (X × ℝ) :=
  (Equiv.ofBijective (graphMap r h) (bijective_graphMap hr hbound)).toHomeomorphOfContinuousClosed
    (continuous_graphMap hh)
    ((continuous_graphMap hh).isClosedMap_of_eqOn_compl_isCompact
      (isCompact_univ.prod (isCompact_Icc (a := -r) (b := r))) (by
        intro z hz
        apply graphMap_eq_self
        have hz' : z.2 ∉ Icc (-r) r := fun ht => hz ⟨mem_univ _, ht⟩
        exact le_of_not_gt (fun ht => hz' ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩)))

@[simp] theorem graphHomeomorph_apply [CompactSpace X] [T2Space X] {r : ℝ}
    (hr : 0 < r) (h : X → ℝ) (hh : Continuous h) (hbound : ∀ x, |h x| < r)
    (z : X × ℝ) : graphHomeomorph hr h hh hbound z = graphMap r h z := rfl

@[simp] theorem graphHomeomorph_zero [CompactSpace X] [T2Space X] {r : ℝ}
    (hr : 0 < r) (h : X → ℝ) (hh : Continuous h) (hbound : ∀ x, |h x| < r)
    (x : X) : graphHomeomorph hr h hh hbound (x, 0) = (x, h x) := by
  simp [graphMap, move_zero hr]

theorem graphHomeomorph_image_zero [CompactSpace X] [T2Space X] {r : ℝ}
    (hr : 0 < r) (h : X → ℝ) (hh : Continuous h) (hbound : ∀ x, |h x| < r) :
    graphHomeomorph hr h hh hbound '' (univ ×ˢ ({0} : Set ℝ)) =
      range (fun x => (x, h x)) := by
  ext z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩
    obtain rfl : t = 0 := ht
    exact ⟨x, (graphHomeomorph_zero hr h hh hbound x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), ⟨mem_univ _, mem_singleton _⟩,
      graphHomeomorph_zero hr h hh hbound x⟩

theorem move_mem_Ioo_iff {r R h t : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hh : |h| < r) : move r h t ∈ Ioo (-R) R ↔ t ∈ Ioo (-R) R := by
  have hm := strictMono_move hr hh
  have hp : move r h R = R := move_eq_self (hrR.trans (le_abs_self R))
  have hn : move r h (-R) = -R := move_eq_self (by simpa using hrR.trans (le_abs_self R))
  have hleft : move r h (-R) < move r h t ↔ -R < t := hm.lt_iff_lt
  have hright : move r h t < move r h R ↔ t < R := hm.lt_iff_lt
  simpa only [hn, hp, mem_Ioo] using and_congr hleft hright

def graphHomeomorphOn [CompactSpace X] [T2Space X] {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (h : X → ℝ) (hh : Continuous h)
    (hbound : ∀ x, |h x| < r) :
    (univ ×ˢ Ioo (-R) R : Set (X × ℝ)) ≃ₜ (univ ×ˢ Ioo (-R) R : Set (X × ℝ)) :=
  (graphHomeomorph hr h hh hbound).subtype (fun z =>
    and_congr Iff.rfl (move_mem_Ioo_iff hr hrR (hbound z.1)).symm)

@[simp] theorem graphHomeomorphOn_apply [CompactSpace X] [T2Space X] {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (h : X → ℝ) (hh : Continuous h)
    (hbound : ∀ x, |h x| < r) (z : (univ ×ˢ Ioo (-R) R : Set (X × ℝ))) :
    (graphHomeomorphOn hr hrR h hh hbound z : X × ℝ) = graphMap r h z := rfl

end Homeomorph.Vertical
