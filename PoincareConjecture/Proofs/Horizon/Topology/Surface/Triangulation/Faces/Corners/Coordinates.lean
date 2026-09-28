import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.VertexCaps

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)

theorem face_frontier_eq_coordinates (i : Bool × Bool) :
    frontier (B.face i).carrier = B.coordinates i ''
      frontier (convexHull ℝ (range (rightTriangleBasis B.scale_pos))) := by
  let C := B.coordinates i
  let A := convexHull ℝ (range (rightTriangleBasis B.scale_pos))
  have hA : IsCompact A := (finite_range (rightTriangleBasis B.scale_pos)).isCompact_convexHull ℝ
  have hsub : A ⊆ C.source := B.triangle_subset_source i
  have himage : C '' A ⊆ C.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.map_source (hsub hz)
  have hcompact := hA.image_of_continuousOn (C.continuousOn.mono hsub)
  have h : C.IsImage A (C '' A) := by
    intro z hz
    constructor
    · rintro ⟨w, hw, heq⟩
      exact C.injOn (hsub hw) hz heq ▸ hw
    · exact mem_image_of_mem C
  rw [B.carrier_eq]
  simpa only [inter_eq_right.mpr (hA.isClosed.frontier_subset.trans hsub),
    inter_eq_right.mpr (hcompact.isClosed.frontier_subset.trans himage)] using
    h.frontier.image_eq.symm

theorem center_mem_frontier (i : Bool × Bool) : p ∈ frontier (B.face i).carrier := by
  apply (B.face i).boundary_image_subset_frontier 2
  rw [B.first_image]
  exact P.mem_firstSide i B.scale_pos.le

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
