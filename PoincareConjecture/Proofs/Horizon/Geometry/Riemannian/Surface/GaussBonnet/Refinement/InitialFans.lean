import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.VertexAncestry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OldVertices
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.EdgeMultiplicity

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

theorem lineRefinementMesh_interior_vertex_fan_of_initial
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (hfan : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 →
      M.position v ∈ interior M.toPlaneComplex.support →
      meshVertexAngleContribution g F M (F (M.position v)) = 2 * Real.pi)
    (u : (M.lineRefinementMesh f).Triangle) (x : (M.lineRefinementMesh f).Vertex)
    (hx : x ∈ u.1)
    (hxint : (M.lineRefinementMesh f).position x ∈
      interior (M.lineRefinementMesh f).toPlaneComplex.support) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f)
      (F ((M.lineRefinementMesh f).position x)) = 2 * Real.pi := by
  rw [M.lineRefinementMesh_support f] at hxint
  obtain ⟨t, ⟨v, hv, hpos⟩ | hcut⟩ := lineRefinementMesh_vertex_old_or_cut M f u x hx
  · rw [hpos] at hxint ⊢
    rw [lineRefinementMesh_vertex_contribution_old_vertex g F M f hF hFi hM t v hv]
    exact hfan t v hv hxint
  · exact lineRefinementMesh_new_vertex_fan g F M f t hcut hxint hF hFi hM

theorem refineByLines_interior_vertex_fan_of_initial
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (hfan : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 →
      M.position v ∈ interior M.toPlaneComplex.support →
      meshVertexAngleContribution g F M (F (M.position v)) = 2 * Real.pi)
    (u : (M.refineByLines lines).Triangle) (x : (M.refineByLines lines).Vertex)
    (hx : x ∈ u.1)
    (hxint : (M.refineByLines lines).position x ∈
      interior (M.refineByLines lines).toPlaneComplex.support) :
    meshVertexAngleContribution g F (M.refineByLines lines)
      (F ((M.refineByLines lines).position x)) = 2 * Real.pi := by
  induction lines generalizing M with
  | nil => exact hfan u x hx hxint
  | cons f fs ih =>
    apply ih (M.lineRefinementMesh f) (by simpa only [M.lineRefinementMesh_support f] using hM)
      (lineRefinementMesh_interior_vertex_fan_of_initial g F M f hF hFi hM hfan) u x hx hxint

theorem single_refineByLines_interior_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (x : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex)
    (hx : x ∈ u.1)
    (hxint : ((TriangleMesh.single b b.ind).refineByLines lines).position x ∈
      interior ((TriangleMesh.single b b.ind).refineByLines lines).toPlaneComplex.support) :
    meshVertexAngleContribution g F ((TriangleMesh.single b b.ind).refineByLines lines)
      (F (((TriangleMesh.single b b.ind).refineByLines lines).position x)) =
        2 * Real.pi := by
  apply refineByLines_interior_vertex_fan_of_initial g F
    (TriangleMesh.single b b.ind) lines hF hFi
    (by simpa only [TriangleMesh.single_support] using hb) ?_ u x hx hxint
  intro t v hv hvint
  rw [TriangleMesh.single_support, b.interior_convexHull] at hvint
  change ∀ i : Fin 3, 0 < b.coord i (b v) at hvint
  have h0 := hvint 0
  have h1 := hvint 1
  fin_cases v
  · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h1
  · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h0
  · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h0

end PoincareConjecture.Topology.Surface
