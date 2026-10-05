import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.PolygonPathCycles
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.SegmentSubdivision

/-!
# The literal midpoint path on a marked segment

Three original segment points give the closing path of a returning
polygon, with its whole carrier and simplicial edge law. See Kneser1929
p.254 and Prime020, literal closing path.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The explicit three-vertex midpoint path has the entire marked
segment as carrier and satisfies the full edge intersection law.
See Prime020, literal closing path. -/
theorem exists_midpoint_segment_path (a b : E) (hab : a ≠ b) :
    ∃ q : Fin 3 → E, Function.Injective q ∧ q 0 = a ∧ q 2 = b ∧
      pathCarrier q = segment ℝ a b ∧
      ∀ i j : Fin 2,
        segment ℝ (q i.castSucc) (q i.succ) ∩ segment ℝ (q j.castSucc) (q j.succ) ⊆
          convexHull ℝ (({q i.castSucc, q i.succ} : Set E) ∩ {q j.castSucc, q j.succ}) := by
  let m := midpoint ℝ a b
  let q : Fin 3 → E := ![a, m, b]
  have hm : Sbtw ℝ a m b := sbtw_midpoint_of_ne ℝ hab
  have ham : a ≠ m := hm.left_ne
  have hmb : m ≠ b := hm.ne_right
  have hqi : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [q]
  have hcarrier : pathCarrier q = segment ℝ a b := by
    calc
      pathCarrier q = segment ℝ a m ∪ segment ℝ m b := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          fin_cases i
          · exact Or.inl hi
          · exact Or.inr hi
        · rintro (hx | hx)
          · exact mem_iUnion.mpr ⟨0, hx⟩
          · exact mem_iUnion.mpr ⟨1, hx⟩
      _ = segment ℝ a b := hm.wbtw.segment_union
  have hcross : segment ℝ a m ∩ segment ℝ m b ⊆ {m} := by
    rintro x ⟨hxa, hxb⟩
    exact (hm.wbtw.trans_left_right (mem_segment_iff_wbtw.mp hxa)).swap_left_iff.mp
      (mem_segment_iff_wbtw.mp hxb)
  have hmix : segment ℝ a m ∩ segment ℝ m b ⊆
      convexHull ℝ (({a, m} : Set E) ∩ {m, b}) := by
    intro x hx
    apply subset_convexHull ℝ _
    exact ⟨Or.inr (hcross hx), Or.inl (hcross hx)⟩
  refine ⟨q, hqi, rfl, rfl, hcarrier, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [inter_self, convexHull_pair]
    exact subset_rfl
  · exact hmix
  · change segment ℝ m b ∩ segment ℝ a m ⊆
      convexHull ℝ (({m, b} : Set E) ∩ {a, m})
    simpa only [inter_comm] using hmix
  · simp only [inter_self, convexHull_pair]
    exact subset_rfl

end Polygon
