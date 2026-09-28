import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineImage










set_option autoImplicit false

open Set

namespace Polygon

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] {n : ℕ}



theorem vertex_mem_boundary (P : Polygon E n) (i : Fin n) : P i ∈ P.boundary ℝ := by
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [edgeSet, affineSegment_eq_segment]
  exact left_mem_segment ℝ _ _




theorem hasSimplicialEdges_affineImage_of_injOn (P : Polygon E n)
    (hP : P.HasSimplicialEdges) (f : E →ᵃ[ℝ] F) (hf : InjOn f (P.boundary ℝ)) :
    (P.affineImage f).HasSimplicialEdges := by
  intro i j
  rw [P.affineImage_edgeSet, P.affineImage_edgeSet,
    P.affineImage_edgeVertices, P.affineImage_edgeVertices]
  rintro y ⟨⟨x, hxi, rfl⟩, z, hzj, hzx⟩
  have hzx' : z = x := hf (mem_iUnion.mpr ⟨j, hzj⟩) (mem_iUnion.mpr ⟨i, hxi⟩) hzx
  subst z
  apply convexHull_mono (image_inter_subset f _ _)
  rw [← f.image_convexHull]
  exact ⟨x, hP i j ⟨hxi, hzj⟩, rfl⟩




theorem affineImage_of_leftInvOn (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (r : E →ᵃ[ℝ] F) (a : F →ᵃ[ℝ] E)
    (hleft : LeftInvOn a r (P.boundary ℝ)) :
    Function.Injective (P.affineImage r) ∧ (P.affineImage r).HasSimplicialEdges ∧
      a '' (P.affineImage r).boundary ℝ = P.boundary ℝ := by
  refine ⟨?_, P.hasSimplicialEdges_affineImage_of_injOn hP r hleft.injOn, ?_⟩
  · intro i j hij
    exact hinj (hleft.injOn (P.vertex_mem_boundary i) (P.vertex_mem_boundary j) hij)
  · rw [P.affineImage_boundary, image_image]
    exact image_congr hleft |>.trans (image_id _)

end Polygon
