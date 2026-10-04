import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonAffineImage

/-!
# Polygon coordinates on an affine slice

An affine projection that is injective on the polygon boundary
preserves its simplicial edge law. An affine inverse on that
boundary recovers the entire original polygon. See Alexander 1924,
pp. 6--7 and M76 derivation 123.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] {n : ℕ}

/-- A polygon vertex belongs to the polygon boundary, including
degenerate polygons. See Alexander p. 6 and derivation 123. -/
theorem vertex_mem_boundary (P : Polygon E n) (i : Fin n) : P i ∈ P.boundary ℝ := by
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [edgeSet, affineSegment_eq_segment]
  exact left_mem_segment ℝ _ _

/-- Injectivity only on the original polygon boundary suffices
for an affine image to retain its edge-intersection law.
See Alexander pp. 6--7 and M76 derivation 123. -/
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

/-- A polygon projection with an inverse on the entire boundary
retains distinct vertices and simplicial edges, and inclusion
recovers its exact boundary. See Alexander pp. 6--7 and derivation 123. -/
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
