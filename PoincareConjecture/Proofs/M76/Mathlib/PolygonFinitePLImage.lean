import PoincareConjecture.Proofs.M76.Mathlib.CommonAffineSegmentPartition
import PoincareConjecture.Proofs.M76.Mathlib.UniformPolygonSimplicity
import PoincareConjecture.Proofs.M76.Mathlib.PolygonEdgeImages










set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}




theorem exists_polygon_finitePL_image (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {f : E → F} {s : Set E} (hf : FinitePiecewiseAffineOn f s)
    (hsub : P.boundary ℝ ⊆ s) (hfi : InjOn f (P.boundary ℝ)) :
    ∃ (N : ℕ) (Q : Polygon F (N + 3)), Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      Q.boundary ℝ = f '' P.boundary ℝ := by
  let a (i : Fin (n + 3)) : ℝ →ᴬ[ℝ] E :=
    ⟨AffineMap.lineMap (P i) (P (finRotate (n + 3) i)),
      (AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) :
        ℝ →ᵃ[ℝ] E).continuous_of_finiteDimensional⟩
  obtain ⟨m, t, ht, ht0, ht1, hformula⟩ := hf.exists_common_affine_segment_partition a
    (fun i r hr => hsub (mem_iUnion.mpr ⟨i, r, hr, rfl⟩))
  let R := P.subdivide t
  have hRi : Function.Injective R := P.injective_subdivide hP hinj t ht ht0 ht1
  have hRs : R.HasSimplicialEdges := P.hasSimplicialEdges_subdivide hP hinj t ht ht0 ht1
  have hRb : R.boundary ℝ = P.boundary ℝ := P.subdivide_boundary t ht ht0 ht1
  let Q : Polygon F ((n + 3) * (m + 1)) := ⟨f ∘ R⟩
  have hQi : Function.Injective Q := by
    intro i j hij
    apply hRi
    apply hfi
    · rw [← hRb]
      exact mem_iUnion.mpr ⟨i, left_mem_affineSegment ℝ _ _⟩
    · rw [← hRb]
      exact mem_iUnion.mpr ⟨j, left_mem_affineSegment ℝ _ _⟩
    · exact hij
  have hedge (k : Fin ((n + 3) * (m + 1))) : Q.edgeSet ℝ k = f '' R.edgeSet ℝ k := by
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨A, hA⟩ := hformula i j
    have hle : t j.castSucc ≤ t j.succ := (ht Fin.castSucc_lt_succ).le
    have hleft := hA (left_mem_Icc.mpr hle)
    have hright := hA (right_mem_Icc.mpr hle)
    change f (a i (t j.castSucc)) = A (t j.castSucc) at hleft
    change f (a i (t j.succ)) = A (t j.succ) at hright
    change affineSegment ℝ (f (P.subdivide t (finProdFinEquiv (i, j))))
      (f (P.subdivide t (finRotate _ (finProdFinEquiv (i, j))))) =
        f '' (P.subdivide t).edgeSet ℝ (finProdFinEquiv (i, j))
    rw [P.subdivide_apply, P.subdivide_rotate_apply t ht0 ht1,
      P.subdivide_edgeSet t ht ht0 ht1]
    change affineSegment ℝ (f (a i (t j.castSucc))) (f (a i (t j.succ))) =
      f '' (a i '' Icc (t j.castSucc) (t j.succ))
    have hseg : A '' affineSegment ℝ (t j.castSucc) (t j.succ) =
        affineSegment ℝ (A (t j.castSucc)) (A (t j.succ)) :=
      affineSegment_image A.toAffineMap _ _
    rw [hleft, hright, ← hseg, affineSegment_eq_segment, segment_eq_Icc hle, image_image]
    exact hA.image_eq.symm
  have hsize : 3 ≤ (n + 3) * (m + 1) :=
    (by omega : 3 ≤ n + 3).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos m))
  have hQs : Q.HasSimplicialEdges := R.hasSimplicialEdges_of_injective_edge_images Q hsize
    hRs hRi f (hRb ▸ hfi) (fun _ => rfl) hedge
  have hQb : Q.boundary ℝ = f '' P.boundary ℝ := by
    rw [← hRb]
    simp only [boundary, hedge, image_iUnion]
  refine ⟨(n + 3) * (m + 1) - 3, ?_⟩
  rw [Nat.sub_add_cancel hsize]
  exact ⟨Q, hQi, hQs, hQb⟩

end Polygon
