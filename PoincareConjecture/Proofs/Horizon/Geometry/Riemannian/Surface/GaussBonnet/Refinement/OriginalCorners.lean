import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OldVertices
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapFaces








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem single_refineByLines_original_corner
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3) :
    meshVertexAngleContribution g F ((TriangleMesh.single b b.ind).refineByLines lines)
      (F (b i)) = coordinateTriangleAngle g F b i := by
  classical
  let t : (TriangleMesh.single b b.ind).Triangle :=
    ⟨Finset.univ, Finset.mem_singleton_self _⟩
  have hpres := refineByLines_vertex_contribution_old_vertex g F (TriangleMesh.single b b.ind)
    lines hF hFi (by simpa only [TriangleMesh.single_support] using hb)
    t i (Finset.mem_univ i)
  change meshVertexAngleContribution g F ((TriangleMesh.single b b.ind).refineByLines lines)
    (F (b i)) = meshVertexAngleContribution g F (TriangleMesh.single b b.ind) (F (b i)) at hpres
  rw [hpres, meshVertexAngleContribution_single]
  have hB : affineBasisOfTriangle b b.ind = b := by ext k; rfl
  rw [hB]
  have hinj : Function.Injective (F ∘ b) := by
    intro j k hjk
    exact b.ind.injective (F.injOn
      (hb (subset_convexHull ℝ _ (mem_range_self j)))
      (hb (subset_convexHull ℝ _ (mem_range_self k))) hjk)
  have heq (j : Fin 3) : F (b j) = F (b i) ↔ j = i :=
    ⟨fun h => hinj h, fun h => h ▸ rfl⟩
  simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)



theorem sum_refined_center_contributions (g : RiemannianMetric 2 S)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ i : Bool, ∑ j : Bool,
      meshVertexAngleContribution g (B.coordinates (i, j))
        ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (i, j))) p) =
      2 * Real.pi := by
  have h (i : Bool × Bool) := single_refineByLines_original_corner g (B.coordinates i)
    (rightTriangleBasis B.scale_pos) (lines i)
    (B.coordinates_smooth i) (B.coordinates_smooth_symm i) (B.triangle_subset_source i) 0
  simp only [B.coordinate_vertex_zero] at h
  simp_rw [h]
  exact B.sum_coordinate_angles g

end ChartCircleArrangementVertexPatch.VertexCapFaces
end PoincareConjecture.Topology.Surface
