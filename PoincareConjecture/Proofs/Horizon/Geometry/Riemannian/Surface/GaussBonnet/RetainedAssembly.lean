import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CoordinateCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilyIncidence








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in


theorem vertex_contribution_eq_parent_sum (g : RiemannianMetric 2 S) (q : S) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      ∑ i : T.Parent, meshVertexAngleContribution g (T.parentCoordinates i)
        (T.refinement.mesh i) q :=
  coordinateVertexAngleContribution_mesh_family g T.parentCoordinates T.refinement.mesh q

omit [T2Space S] in



theorem parent_mesh_vertex_is_used
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (i : T.Parent)
    (hq : q.1 ∈ T.parentCoordinates i '' (T.refinement.mesh i).toPlaneComplex.support) :
    ∃ (t : (T.refinement.mesh i).Triangle) (v : (T.refinement.mesh i).Vertex),
      v ∈ t.1 ∧ T.parentCoordinates i ((T.refinement.mesh i).position v) = q.1 :=
  coordinate_mesh_family_vertex_is_used T.refinement.mesh T.parentCoordinates T.refinement.face
    (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
    T.refinement.boundary_map T.refinement.boundary_injective T.refinement.intersections q i hq

variable [MeasurableSpace S] [BorelSpace S] [T3Space S] [CompactSpace S]



theorem integral_scalarCurvature_eq_euler_add_parent_excess
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    letI := Fintype.ofFinite (Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      4 * Real.pi * ((Nat.card (Euler.CoordinateVertex
        T.refinement.coordinates T.refinement.basis) : ℝ) -
          Nat.card (FaceBoundaryEdge T.refinement.face) + Nat.card T.refinement.Child) +
      2 * (∑ v : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis,
        ((∑ i : T.Parent, meshVertexAngleContribution g (T.parentCoordinates i)
          (T.refinement.mesh i) v.1) - 2 * Real.pi)) := by
  have h := integral_scalarCurvature_eq_euler_add_vertex_excess T.refinement.face
    T.refinement.coordinates T.refinement.basis (fun a => T.parent_smooth a.1)
    (fun a => T.parent_symm_smooth a.1) T.refinement.source_subset T.refinement.carrier_eq
    T.refinement.boundary_map T.refinement.boundary_injective T.refinement.intersections
    T.refinement.intersection_frontier T.refinement.cover D
  simpa only [T.vertex_contribution_eq_parent_sum] using h



theorem integral_scalarCurvature_le_eight_pi_add_parent_excess [ConnectedSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    letI := Fintype.ofFinite (Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi +
      2 * (∑ v : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis,
        ((∑ i : T.Parent, meshVertexAngleContribution g (T.parentCoordinates i)
          (T.refinement.mesh i) v.1) - 2 * Real.pi)) := by
  have h := integral_scalarCurvature_le_eight_pi_add_vertex_excess T.refinement.face
    T.refinement.coordinates T.refinement.basis (fun a => T.parent_smooth a.1)
    (fun a => T.parent_symm_smooth a.1) T.refinement.source_subset T.refinement.carrier_eq
    T.refinement.boundary_map T.refinement.boundary_injective T.refinement.intersections
    T.refinement.intersection_frontier T.refinement.cover D
  simpa only [T.vertex_contribution_eq_parent_sum] using h

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

namespace PoincareConjecture.Topology.Surface

set_option maxHeartbeats 800000 in


theorem exists_retained_scalar_integral_estimate
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [T3Space S] [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
    [CompactSpace S] [ConnectedSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    ∃ T : RetainedCoordinateTriangulation (M := S),
      letI := Fintype.ofFinite (Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
      (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi +
        2 * (∑ v : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis,
          ((∑ i : T.Parent, meshVertexAngleContribution g (T.parentCoordinates i)
            (T.refinement.mesh i) v.1) - 2 * Real.pi)) := by
  obtain ⟨T⟩ := exists_finite_smooth_triangulation_with_retained_coordinates (M := S)
  exact ⟨T, T.integral_scalarCurvature_le_eight_pi_add_parent_excess D⟩

end PoincareConjecture.Topology.Surface
