import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryMultiplicity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.VertexAncestry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OldVertices









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface



theorem affineBasis_vertex_not_mem_open_edge (b : AffineBasis (Fin 3) ℝ Plane)
    (k v : Fin 3) :
    b v ∉ openSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1)) := by
  intro hv
  rw [openSegment_eq_image_lineMap] at hv
  obtain ⟨s, hs, heq⟩ := hv
  have hij : k.succAbove 0 ≠ k.succAbove 1 := by
    intro h
    have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective h
    norm_num at h01
  have hc := congrArg (b.coord (k.succAbove 0)) heq
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
    b.coord_apply_eq, b.coord_apply_ne hij, b.coord_apply] at hc
  split_ifs at hc <;> linarith [hs.1, hs.2]


theorem affineBasis_open_edge_subset_frontier (b : AffineBasis (Fin 3) ℝ Plane)
    (k : Fin 3) :
    openSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1)) ⊆
      frontier (convexHull ℝ (range b)) := by
  rw [frontier_convexHull_affineBasis_fin3_segments]
  intro q hq
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  rw [affineSegment_eq_segment]
  exact openSegment_subset_segment ℝ _ _ hq

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem lineRefinementMesh_boundary_vertex_fan_on
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) (A : Set Plane)
    (hA : A ⊆ (interior M.toPlaneComplex.support)ᶜ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (hfan : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 → M.position v ∈ A →
      meshVertexAngleContribution g F M (F (M.position v)) = Real.pi)
    (u : (M.lineRefinementMesh f).Triangle) (x : (M.lineRefinementMesh f).Vertex)
    (hx : x ∈ u.1) (hxA : (M.lineRefinementMesh f).position x ∈ A) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f)
      (F ((M.lineRefinementMesh f).position x)) = Real.pi := by
  obtain ⟨t, ⟨v, hv, hpos⟩ | hcut⟩ := lineRefinementMesh_vertex_old_or_cut M f u x hx
  · rw [hpos] at hxA ⊢
    rw [lineRefinementMesh_vertex_contribution_old_vertex g F M f hF hFi hM t v hv]
    exact hfan t v hv hxA
  · exact lineRefinementMesh_new_boundary_vertex_fan g F M f t hcut (hA hxA) hF hFi hM



theorem refineByLines_boundary_vertex_fan_on
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (A : Set Plane)
    (hA : A ⊆ (interior M.toPlaneComplex.support)ᶜ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (hfan : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 → M.position v ∈ A →
      meshVertexAngleContribution g F M (F (M.position v)) = Real.pi)
    (u : (M.refineByLines lines).Triangle) (x : (M.refineByLines lines).Vertex)
    (hx : x ∈ u.1) (hxA : (M.refineByLines lines).position x ∈ A) :
    meshVertexAngleContribution g F (M.refineByLines lines)
      (F ((M.refineByLines lines).position x)) = Real.pi := by
  induction lines generalizing M with
  | nil => exact hfan u x hx hxA
  | cons f fs ih =>
    exact ih (M.lineRefinementMesh f)
      (by simpa only [M.lineRefinementMesh_support f] using hA)
      (by simpa only [M.lineRefinementMesh_support f] using hM)
      (lineRefinementMesh_boundary_vertex_fan_on g F M f A hA hF hFi hM hfan) u x hx hxA




theorem single_refineByLines_new_boundary_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (x : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex) (hx : x ∈ u.1)
    (hxboundary : ((TriangleMesh.single b b.ind).refineByLines lines).position x ∉
      interior (convexHull ℝ (range b)))
    (hxnew : ((TriangleMesh.single b b.ind).refineByLines lines).position x ∉ range b) :
    meshVertexAngleContribution g F ((TriangleMesh.single b b.ind).refineByLines lines)
      (F (((TriangleMesh.single b b.ind).refineByLines lines).position x)) = Real.pi := by
  apply refineByLines_boundary_vertex_fan_on g F (TriangleMesh.single b b.ind) lines
    {q | q ∉ interior (convexHull ℝ (range b)) ∧ q ∉ range b}
    (by simpa only [TriangleMesh.single_support] using
      (show {q | q ∉ interior (convexHull ℝ (range b)) ∧ q ∉ range b} ⊆
        (interior (convexHull ℝ (range b)))ᶜ from fun _ h => h.1))
    hF hFi (by simpa only [TriangleMesh.single_support] using hb) ?_ u x hx
    ⟨hxboundary, hxnew⟩
  intro t v hv hvA
  exact False.elim (hvA.2 (mem_range_self v))



theorem single_refineByLines_open_edge_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ)) (k : Fin 3)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (x : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex) (hx : x ∈ u.1)
    (hxedge : ((TriangleMesh.single b b.ind).refineByLines lines).position x ∈
      openSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1))) :
    meshVertexAngleContribution g F ((TriangleMesh.single b b.ind).refineByLines lines)
      (F (((TriangleMesh.single b b.ind).refineByLines lines).position x)) = Real.pi := by
  apply single_refineByLines_new_boundary_vertex_fan g F b lines hF hFi hb u x hx
    (affineBasis_open_edge_subset_frontier b k hxedge).2
  rintro ⟨v, hv⟩
  rw [← hv] at hxedge
  exact affineBasis_vertex_not_mem_open_edge b k v hxedge

end PoincareConjecture.Topology.Surface
