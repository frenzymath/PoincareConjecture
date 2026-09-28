import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.RestrictedFans
import Mathlib.Topology.MetricSpace.Thickening











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface


theorem exists_triangle_interior_containing_bounded {C : Set Plane}
    (hC : Bornology.IsBounded C) :
    ∃ b : AffineBasis (Fin 3) ℝ Plane, C ⊆ interior (convexHull ℝ (range b)) := by
  obtain ⟨b, hb⟩ := exists_triangle_containing_bounded (hC.thickening (δ := 1))
  exact ⟨b, (Metric.self_subset_thickening (by norm_num : (0 : ℝ) < 1) C).trans
    (Metric.isOpen_thickening.subset_interior_iff.mpr hb)⟩

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]




theorem single_refineByLines_restrict_vertex_fan_add_compl
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Triangle)
    (x : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Vertex)
    (hx : x ∈ u.1)
    (hxint : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position x ∈
      interior (convexHull ℝ (range b)))
    (hq : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position x ∈
      F.source) :
    let q := (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position x
    let G := coordinateTangentMetric g F hF hFi q hq
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P) (F q) +
      meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane)
        (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles fun t => ¬P t) q =
          2 * Real.pi := by
  dsimp only
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi _ hq _ hsource,
    meshVertexAngleContribution_restrictTriangles_add_compl]
  apply single_refineByLines_interior_vertex_fan _ (OpenPartialHomeomorph.refl Plane)
    b lines contMDiffOn_id contMDiffOn_id (by simp)
    ⟨u.1, ((((TriangleMesh.single b b.ind).refineByLines lines).mem_restrictTriangles_triangles P).mp u.2).1⟩
    x hx
  simpa only [TriangleMesh.refineByLines_support, TriangleMesh.single_support,
    TriangleMesh.restrictTriangles] using hxint

end PoincareConjecture.Topology.Surface
