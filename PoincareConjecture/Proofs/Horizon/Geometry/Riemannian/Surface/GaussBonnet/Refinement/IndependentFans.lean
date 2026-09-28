import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OriginalCorners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryFans









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem meshVertexAngleContribution_eq_zero_of_not_mem_support
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) {q : S} (hq : q ∉ F '' M.toPlaneComplex.support) :
    meshVertexAngleContribution g F M q = 0 := by
  unfold meshVertexAngleContribution
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  intro heq
  exact hq ⟨meshTriangleBasis M t k,
    meshTriangleBasis_subset_support M t (subset_convexHull ℝ _ (mem_range_self k)), heq⟩



theorem single_refineByLines_contribution_eq_zero_of_not_mem
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    {q : S} (hq : q ∉ F '' convexHull ℝ (range b)) :
    meshVertexAngleContribution g F ((TriangleMesh.single b b.ind).refineByLines lines) q = 0 := by
  apply meshVertexAngleContribution_eq_zero_of_not_mem_support
  simpa only [TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hq




theorem independently_refined_triangle_contribution_at_used_vertex
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (u t : M.Triangle) (v : M.Vertex) (hv : v ∈ u.1)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    meshVertexAngleContribution g F
      ((TriangleMesh.single (meshTriangleBasis M t) (meshTriangleBasis M t).ind).refineByLines lines)
      (F (M.position v)) =
        ∑ k : Fin 3, if F (meshTriangleBasis M t k) = F (M.position v) then
          coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0 := by
  have hq : M.position v ∈ F.source := by
    apply hM
    rw [M.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨u.1, u.2, subset_convexHull ℝ _ ⟨v, hv, rfl⟩⟩
  have hb := (meshTriangleBasis_subset_support M t).trans hM
  by_cases ht : M.position v ∈ convexHull ℝ (range (meshTriangleBasis M t))
  · have hvt := mesh_usedVertex_mem_triangle_of_mem_hull M t u hv ht
    obtain ⟨k, hk⟩ : M.position v ∈ range (meshTriangleBasis M t) := by
      rw [range_meshTriangleBasis]
      exact ⟨v, hvt, rfl⟩
    rw [← hk, single_refineByLines_original_corner g F _ lines hF hFi hb k]
    have heq (j : Fin 3) : F (meshTriangleBasis M t j) = F (meshTriangleBasis M t k) ↔ j = k := by
      constructor
      · intro h
        exact (meshTriangleBasis M t).ind.injective (F.injOn
          (hb (subset_convexHull ℝ _ (mem_range_self j)))
          (hb (subset_convexHull ℝ _ (mem_range_self k))) h)
      · rintro rfl
        rfl
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hout : F (M.position v) ∉ F '' convexHull ℝ (range (meshTriangleBasis M t)) := by
      rintro ⟨z, hz, heq⟩
      exact ht (F.injOn (hb hz) hq heq ▸ hz)
    rw [single_refineByLines_contribution_eq_zero_of_not_mem g F _ lines hout]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro heq
    exact hout ⟨meshTriangleBasis M t k, subset_convexHull ℝ _ (mem_range_self k), heq⟩



theorem independently_refined_mesh_contribution_at_used_vertex
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (lines : M.Triangle → List (Plane →ᵃ[ℝ] ℝ))
    (u : M.Triangle) (v : M.Vertex) (hv : v ∈ u.1) :
    (∑ t : M.Triangle, meshVertexAngleContribution g F
      ((TriangleMesh.single (meshTriangleBasis M t) (meshTriangleBasis M t).ind).refineByLines (lines t))
      (F (M.position v))) = meshVertexAngleContribution g F M (F (M.position v)) := by
  unfold meshVertexAngleContribution
  apply Finset.sum_congr rfl
  intro t _
  exact independently_refined_triangle_contribution_at_used_vertex g F M hF hFi hM
    u t v hv (lines t)

end PoincareConjecture.Topology.Surface
