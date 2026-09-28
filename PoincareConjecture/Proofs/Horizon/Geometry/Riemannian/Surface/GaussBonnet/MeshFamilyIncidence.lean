import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.VertexIncidence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem mesh_exists_used_vertex_of_contribution_ne_zero
    (g : RiemannianMetric 2 S) (M : TriangleMesh) (F : OpenPartialHomeomorph Plane S)
    (q : S) (hq : meshVertexAngleContribution g F M q ≠ 0) :
    ∃ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 ∧ F (M.position v) = q := by
  classical
  by_contra hnone
  apply hq
  unfold meshVertexAngleContribution
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  intro heq
  exact hnone ⟨t, M.orderedVertex t k, M.orderedVertex_mem t k, heq⟩

theorem mesh_used_vertex_preimage (M : TriangleMesh) (F : OpenPartialHomeomorph Plane S)
    (hsource : M.toPlaneComplex.support ⊆ F.source) {z : Plane} (hz : z ∈ F.source)
    (hused : ∃ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 ∧ F (M.position v) = F z) :
    ∃ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 ∧ M.position v = z := by
  obtain ⟨t, v, hv, heq⟩ := hused
  refine ⟨t, v, hv, F.injOn (hsource ?_) hz heq⟩
  rw [TriangleMesh.toPlaneComplex_support]
  exact mem_iUnion₂.mpr ⟨t.1, t.2, subset_convexHull ℝ _ ⟨v, hv, rfl⟩⟩

theorem coordinate_mesh_family_vertex_is_used {I : Type*}
    (M : I → TriangleMesh) (F : I → OpenPartialHomeomorph Plane S)
    (face : ((i : I) × (M i).Triangle) → SmoothFace S)
    (hsource : ∀ i, (M i).toPlaneComplex.support ⊆ (F i).source)
    (hcarrier : ∀ a, (face a).carrier =
      F a.1 '' convexHull ℝ (range (meshTriangleBasis (M a.1) a.2)))
    (hboundary : ∀ a k, ((face a).boundary k).map = F a.1 ∘
      affineChartSegment (meshTriangleBasis (M a.1) a.2 (k.succAbove 0))
        (meshTriangleBasis (M a.1) a.2 (k.succAbove 1)))
    (hinj : ∀ a k, InjOn ((face a).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ a c, a ≠ c →
      (∃ k l : Fin 3, (face a).carrier ∩ (face c).carrier =
          ((face a).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face a).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face c).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face a).carrier ∩ (face c).carrier ⊆
        {F a.1 (meshTriangleBasis (M a.1) a.2 w)})
    (q : Euler.CoordinateVertex (fun a : (i : I) × (M i).Triangle => F a.1)
      (fun a : (i : I) × (M i).Triangle => meshTriangleBasis (M a.1) a.2))
    (i : I) (hq : q.1 ∈ F i '' (M i).toPlaneComplex.support) :
    ∃ (t : (M i).Triangle) (v : (M i).Vertex), v ∈ t.1 ∧ F i ((M i).position v) = q.1 := by
  obtain ⟨z, hz, hzq⟩ := hq
  rw [TriangleMesh.toPlaneComplex_support] at hz
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
  let a : (i : I) × (M i).Triangle := ⟨i, ⟨t, ht⟩⟩
  have hqa : q.1 ∈ (face a).carrier := by
    rw [hcarrier a]
    refine ⟨z, ?_, hzq⟩
    rw [range_meshTriangleBasis]
    exact hzt
  obtain ⟨k, hk, _⟩ := (coordinate_vertex_mem_face_iff face
    (fun a => F a.1) (fun a => meshTriangleBasis (M a.1) a.2)
    (fun a => (meshTriangleBasis_subset_support (M a.1) a.2).trans (hsource a.1))
    hcarrier hboundary hinj hinter q a).mp hqa
  exact ⟨a.2, (M i).orderedVertex a.2 k, (M i).orderedVertex_mem a.2 k, hk⟩

end PoincareConjecture.Topology.Surface
