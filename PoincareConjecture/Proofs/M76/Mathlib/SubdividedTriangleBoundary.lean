import PoincareConjecture.Proofs.M76.Mathlib.SubdividedTrianglePolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangleRegion










set_option autoImplicit false

open Set

private theorem iUnion_integer_intervals (n : ℕ) :
    (⋃ i : Fin (n + 1), Icc (i : ℝ) ((i : ℝ) + 1)) = Icc (0 : ℝ) ((n : ℝ) + 1) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    have hsplit :
        (⋃ i : Fin (n + 2), Icc (i : ℝ) ((i : ℝ) + 1)) =
          (⋃ i : Fin (n + 1), Icc (i : ℝ) ((i : ℝ) + 1)) ∪
            Icc ((n : ℝ) + 1) ((n : ℝ) + 1 + 1) := by
      ext x
      simp only [mem_iUnion, Fin.exists_iff_castSucc, Fin.val_last,
        Fin.val_castSucc, Nat.cast_add, Nat.cast_one, mem_union, or_comm]
    rw [hsplit, ih, Icc_union_Icc_eq_Icc (by positivity) (by linarith)]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem iUnion_horizontal_segments (n : ℕ) :
    (⋃ i : Fin (n + 1), segment ℝ ((i : ℝ), (0 : ℝ)) ((i : ℝ) + 1, 0)) =
      segment ℝ (0, 0) ((n : ℝ) + 1, 0) := by
  let f : ℝ →ᵃ[ℝ] ℝ × ℝ := ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prod 0).toAffineMap
  have hi (a b : ℝ) (hab : a ≤ b) :
      f '' Icc a b = segment ℝ (a, 0) (b, 0) := by
    rw [← segment_eq_Icc hab, image_segment]
    rfl
  simp_rw [← hi _ _ (le_add_of_nonneg_right zero_le_one)]
  rw [← image_iUnion, iUnion_integer_intervals, hi _ _ (by positivity)]

namespace Polygon



def referenceTriangle (n : ℕ) : Polygon (ℝ × ℝ) 3 :=
  ⟨![(0, 0), ((n : ℝ) + 1, 0), (0, 1)]⟩



theorem affineIndependent_referenceTriangle (n : ℕ) :
    AffineIndependent ℝ (referenceTriangle n) := by
  let S : AffineSubspace ℝ (ℝ × ℝ) :=
    (affineSpan ℝ {(0 : ℝ)}).comap (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  have h : AffineIndependent ℝ
      ![((n : ℝ) + 1, (0 : ℝ)), (0, 1), (0, 0)] := by
    apply affineIndependent_of_ne_of_mem_of_notMem_of_mem (s := S)
    · have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
      simpa only [ne_eq, Prod.mk.injEq, and_true] using hn
    · simp [S]
    · simp [S]
    · simp [S]
  exact h.comm_right.comm_left




theorem boundary_subdividedTriangle (n : ℕ) :
    (subdividedTriangle n).boundary ℝ = (referenceTriangle n).boundary ℝ := by
  have hsplit : (subdividedTriangle n).boundary ℝ =
      (⋃ i : Fin (n + 1), segment ℝ ((i : ℝ), 0) ((i : ℝ) + 1, 0)) ∪
        segment ℝ ((n : ℝ) + 1, 0) (0, 1) ∪ segment ℝ (0, 1) (0, 0) := by
    ext x
    simp only [boundary, mem_iUnion, Fin.exists_iff_castSucc,
      subdividedTriangle_edge_last, subdividedTriangle_edge_slope,
      subdividedTriangle_edge_base, mem_union]
    tauto
  rw [hsplit, iUnion_horizontal_segments]
  ext x
  simp [boundary, referenceTriangle, edgeSet, Fin.exists_fin_succ,
    affineSegment_eq_segment, or_assoc]



theorem boundary_subdividedTriangle_eq_frontier (n : ℕ) :
    (subdividedTriangle n).boundary ℝ =
      frontier (convexHull ℝ (range (referenceTriangle n))) := by
  rw [boundary_subdividedTriangle,
    (referenceTriangle n).frontier_convexHull_triangle (affineIndependent_referenceTriangle n)]



theorem closure_inside_subdividedTriangle (n : ℕ) :
    closure (subdividedTriangle n).inside = convexHull ℝ (range (referenceTriangle n)) := by
  have h := affineIndependent_referenceTriangle n
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨referenceTriangle n, h,
    h.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  exact (subdividedTriangle n).closure_inside_eq_of_compact_convex
    (hasSimplicialEdges_subdividedTriangle n) (injective_subdividedTriangle n)
    ((finite_range _).isCompact_convexHull ℝ) (convex_convexHull ℝ _)
    ⟨_, b.centroid_mem_interior_convexHull⟩ (boundary_subdividedTriangle_eq_frontier n).symm

end Polygon
