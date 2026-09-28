import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCompleteFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S] [CompactSpace S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem integral_scalarCurvature_eq_four_pi_euler_of_length_lt_one
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) (hr : T.length < 1) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      4 * Real.pi * ((Nat.card (Euler.CoordinateVertex
        T.refinement.coordinates T.refinement.basis) : ℝ) -
          Nat.card (FaceBoundaryEdge T.refinement.face) + Nat.card T.refinement.Child) := by
  let _ := Fintype.ofFinite (Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
  have hv (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis) :
      (∑ i : T.Parent, meshVertexAngleContribution g (T.parentCoordinates i)
        (T.refinement.mesh i) q.1) = 2 * Real.pi := by
    rw [← T.vertex_contribution_eq_parent_sum]
    exact T.canonical_vertex_fan g hr q
  simpa only [hv, sub_self, Finset.sum_const_zero, mul_zero, add_zero] using
    T.integral_scalarCurvature_eq_euler_add_parent_excess D

theorem integral_scalarCurvature_le_eight_pi_of_length_lt_one [ConnectedSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) (hr : T.length < 1) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi := by
  let _ := Fintype.ofFinite (Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
  have hv (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis) :
      (∑ i : T.Parent, meshVertexAngleContribution g (T.parentCoordinates i)
        (T.refinement.mesh i) q.1) = 2 * Real.pi := by
    rw [← T.vertex_contribution_eq_parent_sum]
    exact T.canonical_vertex_fan g hr q
  simpa only [hv, sub_self, Finset.sum_const_zero, mul_zero, add_zero] using
    T.integral_scalarCurvature_le_eight_pi_add_parent_excess D

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
