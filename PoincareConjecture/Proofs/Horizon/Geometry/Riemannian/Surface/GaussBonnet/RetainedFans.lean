import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAssembly
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapEdgeFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.IndependentFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.IndependentNewVertices
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.ComplementFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in

theorem cap_center_contribution (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) :
    (∑ i : Bool, ∑ j : Bool, meshVertexAngleContribution g ((T.caps p).coordinates (i, j))
      (T.refinement.mesh (.inl (p, (i, j)))) (p : S)) = 2 * Real.pi := by
  have heq (s : Bool × Bool) : T.refinement.mesh (.inl (p, s)) =
      (TriangleMesh.single (rightTriangleBasis (T.caps p).scale_pos)
        (rightTriangleBasis (T.caps p).scale_pos).ind).refineByLines
          (T.refinement.subdivision (.inl (p, s))).refinement_lines :=
    (T.refinement.subdivision (.inl (p, s))).mesh_eq_refineByLines
  simp_rw [heq]
  exact (T.caps p).sum_refined_center_contributions g
    (fun s => (T.refinement.subdivision (.inl (p, s))).refinement_lines)

theorem cap_contribution_away_from_original_vertices (g : RiemannianMetric 2 S)
    (p : T.decomposition.vertices)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : ∃ i, q.1 ∈ ((T.caps p).face i).carrier) (hcenter : q.1 ≠ (p : S))
    (hfirst : ∀ i, q.1 ≠ (T.caps p).firstOuterTip i)
    (hsecond : ∀ i, q.1 ≠ (T.caps p).secondOuterTip i) :
    (∑ i : Bool × Bool, meshVertexAngleContribution g ((T.caps p).coordinates i)
      (T.refinement.mesh (.inl (p, i))) q.1) =
      if ∃ (i : Bool × Bool) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧
        (((T.caps p).face i).boundary 0).map t = q.1 then Real.pi else 2 * Real.pi := by
  have heq (i : Bool × Bool) : T.refinement.mesh (.inl (p, i)) =
      (TriangleMesh.single (rightTriangleBasis (T.caps p).scale_pos)
        (rightTriangleBasis (T.caps p).scale_pos).ind).refineByLines
          (T.refinement.subdivision (.inl (p, i))).refinement_lines :=
    (T.refinement.subdivision (.inl (p, i))).mesh_eq_refineByLines
  have hused (i : Bool × Bool) (hi : q.1 ∈ ((T.caps p).face i).carrier) :
      ∃ (t : (T.refinement.mesh (.inl (p, i))).Triangle)
        (v : (T.refinement.mesh (.inl (p, i))).Vertex),
        v ∈ t.1 ∧ (T.caps p).coordinates i ((T.refinement.mesh (.inl (p, i))).position v) = q.1 := by
    apply T.parent_mesh_vertex_is_used q (.inl (p, i))
    change q.1 ∈ (T.caps p).coordinates i '' (T.refinement.mesh (.inl (p, i))).toPlaneComplex.support
    rw [(T.refinement.subdivision (.inl (p, i))).support]
    exact (T.caps p).carrier_eq i ▸ hi
  simp_rw [heq]
  apply (T.caps p).refined_vertex_fan_away_from_original_vertices g
    (fun i => (T.refinement.subdivision (.inl (p, i))).refinement_lines)
    hq hcenter hfirst hsecond
  intro i hi
  have hw := hused i hi
  rw [heq i] at hw
  exact hw

omit [T2Space S] in

theorem core_contribution_at_used_vertex (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (u : (T.refined.mesh R).Triangle)
    (v : (T.refined.mesh R).Vertex) (hv : v ∈ u.1) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩)))
        ((chartAt Plane (T.chart R : S)).symm ((T.refined.mesh R).position v))) =
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R)
        ((chartAt Plane (T.chart R : S)).symm ((T.refined.mesh R).position v)) := by
  have heq (t : (T.refined.mesh R).Triangle) : T.refinement.mesh (.inr (.inr ⟨R, t⟩)) =
      (TriangleMesh.single (meshTriangleBasis (T.refined.mesh R) t)
        (meshTriangleBasis (T.refined.mesh R) t).ind).refineByLines
          (T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).mesh_eq_refineByLines
  simp_rw [heq]
  exact independently_refined_mesh_contribution_at_used_vertex g
    (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R)
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞)) (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    (T.refined.source R) _ u v hv

omit [T2Space S] in

theorem core_mesh_interior_fan (g : RiemannianMetric 2 S) (R : T.decomposition.regions)
    (t : (T.refined.mesh R).Triangle) (v : (T.refined.mesh R).Vertex) (hv : v ∈ t.1)
    (hint : (T.refined.mesh R).position v ∈ interior (T.refined.mesh R).toPlaneComplex.support) :
    meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R)
      ((chartAt Plane (T.chart R : S)).symm ((T.refined.mesh R).position v)) = 2 * Real.pi := by
  have hsource : (T.coreMeshes R).toPlaneComplex.support ⊆ (chartAt Plane (T.chart R : S)).target := by
    rw [← T.refined.support R]
    exact T.refined.source R
  have hfan : ∀ (s : (T.coreMeshes R).Triangle) (w : (T.coreMeshes R).Vertex), w ∈ s.1 →
      (T.coreMeshes R).position w ∈ interior (T.coreMeshes R).toPlaneComplex.support →
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm (T.coreMeshes R)
        ((chartAt Plane (T.chart R : S)).symm ((T.coreMeshes R).position w)) = 2 * Real.pi := by
    obtain ⟨b, lines, P, heq, _⟩ := T.core_ancestry R
    rw [heq] at hsource ⊢
    exact fun s w hw hi => single_refineByLines_restrict_interior_vertex_fan_of_source
      g (chartAt Plane (T.chart R : S)).symm b lines P
      (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
      (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) hsource s w hw hi
  have heq := T.refined.mesh_eq_refineByLines R
  revert t v
  rw [heq]
  intro t v hv hint
  exact refineByLines_interior_vertex_fan_of_initial g (chartAt Plane (T.chart R : S)).symm
    (T.coreMeshes R) _ (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) hsource hfan t v hv hint

omit [T2Space S] in

theorem core_contribution_at_used_interior_vertex (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (t : (T.refined.mesh R).Triangle)
    (v : (T.refined.mesh R).Vertex) (hv : v ∈ t.1)
    (hint : (T.refined.mesh R).position v ∈ interior (T.refined.mesh R).toPlaneComplex.support) :
    (∑ u : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, u⟩)))
        ((chartAt Plane (T.chart R : S)).symm ((T.refined.mesh R).position v))) = 2 * Real.pi := by
  rw [T.core_contribution_at_used_vertex g R t v hv]
  exact T.core_mesh_interior_fan g R t v hv hint

set_option maxHeartbeats 800000 in
omit [T2Space S] in

theorem core_parent_used_vertex
    (R : T.decomposition.regions)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {z : Plane} (hz : (chartAt Plane (T.chart R : S)).symm z = q.1)
    (t : (T.refined.mesh R).Triangle)
    (ht : z ∈ convexHull ℝ (range (meshTriangleBasis (T.refined.mesh R) t))) :
    ∃ (u : (T.refinement.mesh (.inr (.inr ⟨R, t⟩))).Triangle)
      (v : (T.refinement.mesh (.inr (.inr ⟨R, t⟩))).Vertex),
      v ∈ u.1 ∧ (T.refinement.mesh (.inr (.inr ⟨R, t⟩))).position v = z := by
  have hsupport : z ∈ (T.refinement.mesh (.inr (.inr ⟨R, t⟩))).toPlaneComplex.support := by
    rw [(T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).support]
    exact ht
  let i : T.Parent := .inr (.inr ⟨R, t⟩)
  have himage : q.1 ∈ T.parentCoordinates i '' (T.refinement.mesh i).toPlaneComplex.support :=
    ⟨z, hsupport, hz⟩
  apply mesh_used_vertex_preimage (T.refinement.mesh i) (T.parentCoordinates i)
    (T.refinement.mesh_source T.parent_source i)
    (T.refined.source R (meshTriangleBasis_subset_support _ t ht))
  rw [show T.parentCoordinates i z = q.1 from hz]
  exact T.parent_mesh_vertex_is_used q i himage

set_option maxHeartbeats 800000 in
omit [T2Space S] in

theorem core_contribution_at_interior_canonical_vertex (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (chartAt Plane (T.chart R : S)).symm ''
      interior (T.refined.mesh R).toPlaneComplex.support) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q.1) = 2 * Real.pi := by
  obtain ⟨z, hz, hez⟩ := hq
  have heq (t : (T.refined.mesh R).Triangle) : T.refinement.mesh (.inr (.inr ⟨R, t⟩)) =
      (TriangleMesh.single (meshTriangleBasis (T.refined.mesh R) t)
        (meshTriangleBasis (T.refined.mesh R) t).ind).refineByLines
          (T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).mesh_eq_refineByLines
  simp_rw [heq]
  rw [← hez]
  apply independently_refined_mesh_interior_vertex_fan g (chartAt Plane (T.chart R : S)).symm
    (T.refined.mesh R) (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) (T.refined.source R) _
    (T.core_mesh_interior_fan g R) hz
  intro t ht
  have hw := T.core_parent_used_vertex R q hez t ht
  rw [heq t] at hw
  exact hw

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
