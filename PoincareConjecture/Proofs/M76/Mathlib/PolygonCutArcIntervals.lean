import PoincareConjecture.Proofs.M76.Mathlib.PolygonInteriorCutArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearChain










set_option autoImplicit false

open Set Geometry AffineMap

namespace Set




theorem isFinitePLBallPair_two_segments
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b c : E} (hab : a ≠ b) (hbc : b ≠ c)
    (hinter : segment ℝ a b ∩ segment ℝ b c = {b}) :
    IsFinitePLBallPair ℝ (segment ℝ a b ∪ segment ℝ b c) {a, c} := by
  have hac : a ≠ c := by
    intro hac
    have h : a ∈ segment ℝ a b ∩ segment ℝ b c :=
      ⟨left_mem_segment ℝ a b, hac.symm ▸ right_mem_segment ℝ b c⟩
    exact hab (hinter.subset h)
  let p : Fin 3 → E := ![a, b, c]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  have hchain (i j : Fin 2) :
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩ {p j.castSucc, p j.succ}) := by
    fin_cases i <;> fin_cases j
    · change segment ℝ a b ∩ segment ℝ a b ⊆
        convexHull ℝ (({a, b} : Set E) ∩ {a, b})
      simp only [inter_self, convexHull_pair, subset_refl]
    · intro x hx
      have hxb : x = b := hinter.subset hx
      apply subset_convexHull ℝ _
      simp [p, hxb]
    · intro x hx
      have hxb : x = b := hinter.subset ⟨hx.2, hx.1⟩
      apply subset_convexHull ℝ _
      simp [p, hxb]
    · change segment ℝ b c ∩ segment ℝ b c ⊆
        convexHull ℝ (({b, c} : Set E) ∩ {b, c})
      simp only [inter_self, convexHull_pair, subset_refl]
  have h := isFinitePLBallPair_linear_chain p hp hchain
  have hcarrier : (⋃ i : Fin 2, segment ℝ (p i.castSucc) (p i.succ)) =
      segment ℝ a b ∪ segment ℝ b c := by
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
  rw [hcarrier] at h
  exact h

end Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}




theorem cutArc_eq_segments (P : Polygon E n) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    P.cutArc t i = segment ℝ (P.edgeCut t i) (P (finRotate n i)) ∪
      segment ℝ (P (finRotate n i)) (P.edgeCut t (finRotate n i)) := by
  have htail : lineMap (P i) (P (finRotate n i)) '' Icc (t i) 1 =
      segment ℝ (P.edgeCut t i) (P (finRotate n i)) := by
    rw [← segment_eq_Icc (ht i).2, ← affineSegment_eq_segment, affineSegment_image,
      lineMap_apply_one, affineSegment_eq_segment]
    rfl
  have hhead : lineMap (P (finRotate n i)) (P (finRotate n (finRotate n i))) ''
      Icc 0 (t (finRotate n i)) =
        segment ℝ (P (finRotate n i)) (P.edgeCut t (finRotate n i)) := by
    rw [← segment_eq_Icc (ht _).1, ← affineSegment_eq_segment, affineSegment_image,
      lineMap_apply_zero, affineSegment_eq_segment]
    rfl
  exact congrArg₂ (· ∪ ·) htail hhead





theorem cutArc_ballPair [FiniteDimensional ℝ E]
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (i : Fin (n + 3)) :
    IsFinitePLBallPair ℝ (P.cutArc t i)
      {P.edgeCut t i, P.edgeCut t (finRotate (n + 3) i)} := by
  let j := finRotate (n + 3) i
  have htc (k) : t k ∈ Icc (0 : ℝ) 1 := ⟨(ht k).1.le, (ht k).2.le⟩
  have hleft : segment ℝ (P.edgeCut t i) (P j) ⊆ P.edgeSet ℝ i := by
    change segment ℝ (P.edgeCut t i) (P j) ⊆ affineSegment ℝ (P i) (P j)
    rw [affineSegment_eq_segment]
    exact (convex_segment (𝕜 := ℝ) (P i) (P j)).segment_subset
      (lineMap_mem_segment ℝ (P i) (P j) (htc i)) (right_mem_segment ℝ (P i) (P j))
  have hright : segment ℝ (P j) (P.edgeCut t j) ⊆ P.edgeSet ℝ j := by
    change segment ℝ (P j) (P.edgeCut t j) ⊆
      affineSegment ℝ (P j) (P (finRotate (n + 3) j))
    rw [affineSegment_eq_segment]
    exact (convex_segment (𝕜 := ℝ) (P j) (P (finRotate (n + 3) j))).segment_subset
      (left_mem_segment ℝ (P j) (P (finRotate (n + 3) j)))
      (lineMap_mem_segment ℝ (P j) (P (finRotate (n + 3) j)) (htc j))
  have hinter : segment ℝ (P.edgeCut t i) (P j) ∩
      segment ℝ (P j) (P.edgeCut t j) = {P j} := by
    apply Subset.antisymm
    · exact (inter_subset_inter hleft hright).trans
        (P.adjacent_edgeSet_inter hP hinj i).subset
    · rintro x rfl
      exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩
  have hleftne : P.edgeCut t i ≠ P j := fun h =>
    P.edgeCut_notMem_range hP hinj t (ht i) ⟨j, h.symm⟩
  have hrightne : P j ≠ P.edgeCut t j := fun h =>
    P.edgeCut_notMem_range hP hinj t (ht j) ⟨j, h⟩
  rw [P.cutArc_eq_segments t htc i]
  exact isFinitePLBallPair_two_segments hleftne hrightne hinter

end Polygon
