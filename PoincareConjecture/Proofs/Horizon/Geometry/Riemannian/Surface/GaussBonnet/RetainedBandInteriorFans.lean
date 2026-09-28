import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAssembly
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilySeparation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.InteriorFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.IndependentFans








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in

theorem band_parent_support_union (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count) :
    (⋃ a : Fin (T.bands p i).faces.interface.count × Bool,
      T.parentCoordinates (.inr (.inl ⟨⟨p, i⟩, a⟩)) ''
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).toPlaneComplex.support) =
      (T.bands p i).faces.carrier := by
  apply iUnion_congr
  intro a
  rw [(T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).support,
    (T.bands p i).faces.face_carrier_eq_coordinates a]
  rfl


theorem vertex_contribution_eq_band_sum_of_interior
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count) {q : S}
    (hq : q ∈ interior (T.bands p i).faces.carrier) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      ∑ a : Fin (T.bands p i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates a)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))) q := by
  rw [T.vertex_contribution_eq_parent_sum]
  symm
  apply Fintype.sum_of_injective
    (fun a : Fin (T.bands p i).faces.interface.count × Bool =>
      (.inr (.inl ⟨⟨p, i⟩, a⟩) : T.Parent))
  · intro a b h
    simpa using h
  · intro a ha
    apply meshVertexAngleContribution_eq_zero_of_not_mem_support
    apply coordinate_mesh_family_not_mem_of_interior_subfamily
      T.refinement.mesh T.parentCoordinates T.refinement.face
      (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
      T.refinement.intersection_frontier
      (fun b : Fin (T.bands p i).faces.interface.count × Bool => .inr (.inl ⟨⟨p, i⟩, b⟩)) a
      (fun b h => ha ⟨b, h.symm⟩)
    rwa [T.band_parent_support_union]
  · intro a
    rfl



theorem band_contribution_at_interior_canonical_vertex
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ interior (T.bands p i).faces.carrier) :
    (∑ a : Fin (T.bands p i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates a)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))) q.1) = 2 * Real.pi := by
  have heq (a : Fin (T.bands p i).faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩)) =
        (TriangleMesh.single ((T.bands p i).faces.faceBasis a)
          ((T.bands p i).faces.faceBasis a).ind).refineByLines
            (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).mesh_eq_refineByLines
  have hused (a : Fin (T.bands p i).faces.interface.count × Bool)
      (ha : q.1 ∈ ((T.bands p i).faces.face a).carrier) :
      ∃ (t : (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).Triangle)
        (v : (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).Vertex),
        v ∈ t.1 ∧ (T.bands p i).faces.faceCoordinates a
          ((T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).position v) = q.1 := by
    apply T.parent_mesh_vertex_is_used q (.inr (.inl ⟨⟨p, i⟩, a⟩))
    change q.1 ∈ (T.bands p i).faces.faceCoordinates a ''
      (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).toPlaneComplex.support
    rw [(T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).support]
    exact (T.bands p i).faces.face_carrier_eq_coordinates a ▸ ha
  have hcoord := linearGraphCoordinates_contMDiff
    (chartAt Plane (T.chart p.1.1 : S)).symm ((T.graphs p).piece i).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  simp_rw [heq]
  apply (T.bands p i).faces.interior_refined_vertex_fan g hcoord.1 hcoord.2 _ hq
  intro a ha
  have hw := hused a ha
  rw [heq a] at hw
  exact hw



theorem canonical_vertex_fan_of_band_interior
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ interior (T.bands p i).faces.carrier) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  rw [T.vertex_contribution_eq_band_sum_of_interior g p i hq]
  exact T.band_contribution_at_interior_canonical_vertex g p i q hq

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
