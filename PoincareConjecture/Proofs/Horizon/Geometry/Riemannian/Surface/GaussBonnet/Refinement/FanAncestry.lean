import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryMultiplicity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OldVertices
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.VertexAncestry

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

theorem lineRefinementMesh_new_vertex_contribution
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f) (F q) =
      if q ∈ interior M.toPlaneComplex.support then 2 * Real.pi else Real.pi := by
  split_ifs with h
  · exact lineRefinementMesh_new_vertex_fan g F M f t hq h hF hFi hM
  · exact lineRefinementMesh_new_boundary_vertex_fan g F M f t hq h hF hFi hM

theorem refineByLines_vertex_contribution_old_or_new
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (u : (M.refineByLines lines).Triangle) (x : (M.refineByLines lines).Vertex)
    (hx : x ∈ u.1) :
    (∃ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 ∧
      M.position v = (M.refineByLines lines).position x ∧
      meshVertexAngleContribution g F (M.refineByLines lines)
        (F ((M.refineByLines lines).position x)) =
          meshVertexAngleContribution g F M (F ((M.refineByLines lines).position x))) ∨
    meshVertexAngleContribution g F (M.refineByLines lines)
      (F ((M.refineByLines lines).position x)) =
        if (M.refineByLines lines).position x ∈ interior M.toPlaneComplex.support
        then 2 * Real.pi else Real.pi := by
  induction lines generalizing M with
  | nil => exact Or.inl ⟨u, x, hx, rfl, rfl⟩
  | cons f fs ih =>
    dsimp only [TriangleMesh.refineByLines]
    have hM' : (M.lineRefinementMesh f).toPlaneComplex.support ⊆ F.source := by
      simpa only [M.lineRefinementMesh_support f] using hM
    rcases ih (M.lineRefinementMesh f) hM' u x hx with ⟨t, v, hv, hpos, hcontrib⟩ | hnew
    · obtain ⟨s, ⟨w, hw, hwpos⟩ | hcut⟩ :=
        lineRefinementMesh_vertex_old_or_cut M f t v hv
      · left
        refine ⟨s, w, hw, hwpos.symm.trans hpos, ?_⟩
        rw [hcontrib, ← hpos, hwpos]
        exact lineRefinementMesh_vertex_contribution_old_vertex g F M f hF hFi hM s w hw
      · right
        rw [hcontrib]
        simpa only [hpos] using
          lineRefinementMesh_new_vertex_contribution g F M f s hcut hF hFi hM
    · right
      simpa only [M.lineRefinementMesh_support f] using hnew

theorem refineByLines_new_used_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (u : (M.refineByLines lines).Triangle) (x : (M.refineByLines lines).Vertex)
    (hx : x ∈ u.1)
    (hnew : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 →
      M.position v ≠ (M.refineByLines lines).position x) :
    meshVertexAngleContribution g F (M.refineByLines lines)
      (F ((M.refineByLines lines).position x)) =
        if (M.refineByLines lines).position x ∈ interior M.toPlaneComplex.support
        then 2 * Real.pi else Real.pi := by
  rcases refineByLines_vertex_contribution_old_or_new g F M lines hF hFi hM u x hx with
    ⟨t, v, hv, hpos, _⟩ | hfan
  · exact False.elim (hnew t v hv hpos)
  · exact hfan

end PoincareConjecture.Topology.Surface
