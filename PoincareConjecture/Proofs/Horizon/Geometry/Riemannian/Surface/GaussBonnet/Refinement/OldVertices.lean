import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Incidence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface



theorem lineRefinementMesh_oldVertex_mem_triangle (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) (v : M.Vertex) (hv : v ∈ t.1) :
    ∃ u : (M.lineRefinementMesh f).Triangle, M.oldRefinedVertex f v ∈ u.1 := by
  obtain ⟨i, rfl⟩ := (M.range_orderedVertex t ▸ hv : v ∈ range (M.orderedVertex t))
  have hmem : M.position (M.orderedVertex t i) ∈
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) :=
    subset_convexHull ℝ _ ⟨_, M.orderedVertex_mem t i, rfl⟩
  rw [← M.localMeshTriangles_support f t] at hmem
  obtain ⟨s, hmem⟩ := mem_iUnion.mp hmem
  obtain ⟨hs, hmem⟩ := mem_iUnion.mp hmem
  exact ⟨⟨s, M.mem_lineRefinementTriangles_iff f |>.mpr ⟨t, hs⟩⟩,
    M.old_vertex_mem_child_of_position_mem f t i hs hmem⟩



theorem refineByLines_exists_usedVertex (M : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (t : M.Triangle) (v : M.Vertex) (hv : v ∈ t.1) :
    ∃ u : (M.refineByLines lines).Triangle,
      ∃ w : (M.refineByLines lines).Vertex, w ∈ u.1 ∧
        (M.refineByLines lines).position w = M.position v := by
  induction lines generalizing M with
  | nil => exact ⟨t, v, hv, rfl⟩
  | cons f fs ih =>
    obtain ⟨u, hu⟩ := lineRefinementMesh_oldVertex_mem_triangle M f t v hv
    exact ih (M.lineRefinementMesh f) u (M.oldRefinedVertex f v) hu

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem lineRefinementMesh_vertex_contribution_old_vertex
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (t : M.Triangle) (v : M.Vertex) (hv : v ∈ t.1) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f) (F (M.position v)) =
      meshVertexAngleContribution g F M (F (M.position v)) := by
  have hvsource : M.position v ∈ F.source := by
    apply hM
    apply meshTriangleBasis_subset_support M t
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  rw [lineRefinementMesh_vertex_contribution g F M f hF hFi hM, add_eq_left]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro q hq
  have hqu := List.mem_toFinset.mp hq
  have hqsource : q ∈ F.source := hM (meshTriangleBasis_subset_support M u
    (((finite_range _).isClosed_convexHull ℝ).frontier_subset
      (localRefinementBoundaryCuts_geometry M f u hqu).1))
  rw [if_neg]
  intro heq
  exact localRefinementBoundaryCuts_ne_usedVertex M f u hqu t v hv
    (F.injOn hqsource hvsource heq)



theorem refineByLines_vertex_contribution_old_vertex
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (t : M.Triangle) (v : M.Vertex) (hv : v ∈ t.1) :
    meshVertexAngleContribution g F (M.refineByLines lines) (F (M.position v)) =
      meshVertexAngleContribution g F M (F (M.position v)) := by
  induction lines generalizing M with
  | nil => rfl
  | cons f fs ih =>
    obtain ⟨u, hu⟩ := lineRefinementMesh_oldVertex_mem_triangle M f t v hv
    have hsource : (M.lineRefinementMesh f).toPlaneComplex.support ⊆ F.source := by
      rw [M.lineRefinementMesh_support f]
      exact hM
    change meshVertexAngleContribution g F ((M.lineRefinementMesh f).refineByLines fs)
      (F ((M.lineRefinementMesh f).position (M.oldRefinedVertex f v))) = _
    rw [ih (M.lineRefinementMesh f) hsource u (M.oldRefinedVertex f v) hu]
    exact lineRefinementMesh_vertex_contribution_old_vertex g F M f hF hFi hM t v hv

end PoincareConjecture.Topology.Surface
