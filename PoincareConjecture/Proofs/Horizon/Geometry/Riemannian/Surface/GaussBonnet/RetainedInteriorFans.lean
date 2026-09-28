import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilySeparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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

theorem core_parent_support_union (R : T.decomposition.regions) :
    (⋃ t : (T.refined.mesh R).Triangle,
      T.parentCoordinates (.inr (.inr ⟨R, t⟩)) ''
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))).toPlaneComplex.support) =
      (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support := by
  calc
    _ = ⋃ t : (T.refined.mesh R).Triangle,
        (chartAt Plane (T.chart R : S)).symm '' convexHull ℝ (range (meshTriangleBasis (T.refined.mesh R) t)) := by
      apply iUnion_congr
      intro t
      rw [(T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).support]
      rfl
    _ = _ := by rw [← image_iUnion, meshTriangleBasis_sources_cover]

theorem other_parent_contribution_eq_zero_in_core_interior
    (g : RiemannianMetric 2 S) (R : T.decomposition.regions) {q : S}
    (hq : q ∈ (chartAt Plane (T.chart R : S)).symm ''
      interior (T.refined.mesh R).toPlaneComplex.support)
    (i : T.Parent) (hi : ∀ t : (T.refined.mesh R).Triangle, i ≠ .inr (.inr ⟨R, t⟩)) :
    meshVertexAngleContribution g (T.parentCoordinates i) (T.refinement.mesh i) q = 0 := by
  apply meshVertexAngleContribution_eq_zero_of_not_mem_support
  apply coordinate_mesh_family_not_mem_of_interior_subfamily
    T.refinement.mesh T.parentCoordinates T.refinement.face
    (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
    T.refinement.intersection_frontier (fun t : (T.refined.mesh R).Triangle => .inr (.inr ⟨R, t⟩)) i hi
  rw [T.core_parent_support_union,
    interior_smooth_coordinate_image _ (T.refined.source R)]
  exact hq

theorem canonical_vertex_fan_in_core_interior
    (g : RiemannianMetric 2 S) (R : T.decomposition.regions)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (chartAt Plane (T.chart R : S)).symm ''
      interior (T.refined.mesh R).toPlaneComplex.support) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  rw [T.vertex_contribution_eq_parent_sum]
  have hsum : (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q.1) =
      ∑ i : T.Parent, meshVertexAngleContribution g (T.parentCoordinates i)
        (T.refinement.mesh i) q.1 := by
    apply Fintype.sum_of_injective (fun t : (T.refined.mesh R).Triangle =>
      (Sum.inr (Sum.inr ⟨R, t⟩) : T.Parent))
    · intro t u h
      simpa only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
    · intro i hi
      exact T.other_parent_contribution_eq_zero_in_core_interior g R hq i
        (fun t ht => hi ⟨t, ht.symm⟩)
    · intro t
      rfl
  rw [← hsum]
  exact T.core_contribution_at_interior_canonical_vertex g R q hq

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
