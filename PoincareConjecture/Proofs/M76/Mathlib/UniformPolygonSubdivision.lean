import PoincareConjecture.Proofs.M76.Mathlib.FinProductRotation
import PoincareConjecture.Proofs.M76.Mathlib.FiniteOrderedPartition
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n m : ℕ}

def subdivide (P : Polygon E n) (t : Fin (m + 2) → ℝ) : Polygon E (n * (m + 1)) :=
  ⟨fun k => let ij := finProdFinEquiv.symm k
    AffineMap.lineMap (P ij.1) (P (finRotate n ij.1)) (t ij.2.castSucc)⟩

theorem subdivide_apply (P : Polygon E n) (t : Fin (m + 2) → ℝ)
    (i : Fin n) (j : Fin (m + 1)) :
    P.subdivide t (finProdFinEquiv (i, j)) =
      AffineMap.lineMap (P i) (P (finRotate n i)) (t j.castSucc) := by
  exact congrArg (fun ij : Fin n × Fin (m + 1) =>
    AffineMap.lineMap (P ij.1) (P (finRotate n ij.1)) (t ij.2.castSucc))
      (finProdFinEquiv.symm_apply_apply (i, j))

theorem subdivide_rotate_apply (P : Polygon E n) (t : Fin (m + 2) → ℝ)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last (m + 1)) = 1)
    (i : Fin n) (j : Fin (m + 1)) :
    P.subdivide t (finRotate (n * (m + 1)) (finProdFinEquiv (i, j))) =
      AffineMap.lineMap (P i) (P (finRotate n i)) (t j.succ) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [finRotate_finProdFinEquiv_last, subdivide_apply]
    change AffineMap.lineMap _ _ (t 0) = AffineMap.lineMap _ _ (t (Fin.last (m + 1)))
    rw [ht0, ht1, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  · rw [finRotate_finProdFinEquiv_castSucc, subdivide_apply]
    rfl

theorem subdivide_edgeSet (P : Polygon E n) (t : Fin (m + 2) → ℝ)
    (ht : StrictMono t) (ht0 : t 0 = 0) (ht1 : t (Fin.last (m + 1)) = 1)
    (i : Fin n) (j : Fin (m + 1)) :
    (P.subdivide t).edgeSet ℝ (finProdFinEquiv (i, j)) =
      AffineMap.lineMap (P i) (P (finRotate n i)) '' Icc (t j.castSucc) (t j.succ) := by
  rw [edgeSet, subdivide_apply, subdivide_rotate_apply P t ht0 ht1]
  rw [← affineSegment_image, affineSegment_eq_segment, segment_eq_Icc (ht Fin.castSucc_lt_succ).le]

theorem subdivide_boundary (P : Polygon E n) (t : Fin (m + 2) → ℝ)
    (ht : StrictMono t) (ht0 : t 0 = 0) (ht1 : t (Fin.last (m + 1)) = 1) :
    (P.subdivide t).boundary ℝ = P.boundary ℝ := by
  have hmem (j : Fin (m + 2)) : t j ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le _)
    · rw [← ht1]
      exact ht.monotone (Fin.le_last _)
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [P.subdivide_edgeSet t ht ht0 ht1] at hk
    obtain ⟨r, hr, rfl⟩ := hk
    exact mem_iUnion.mpr ⟨i, r, ⟨(hmem _).1.trans hr.1, hr.2.trans (hmem _).2⟩, rfl⟩
  · intro hx
    obtain ⟨i, r, hr, rfl⟩ := mem_iUnion.mp hx
    have hr' : r ∈ Icc (t 0) (t (Fin.last (m + 1))) := by rwa [ht0, ht1]
    obtain ⟨j, hj⟩ := ht.monotone.exists_mem_consecutive_Icc hr'
    apply mem_iUnion.mpr
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    rw [P.subdivide_edgeSet t ht ht0 ht1]
    exact ⟨r, hj, rfl⟩

end Polygon
