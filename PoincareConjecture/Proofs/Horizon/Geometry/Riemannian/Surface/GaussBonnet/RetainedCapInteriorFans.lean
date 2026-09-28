import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilySeparation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapUnionFrontier








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

theorem cap_parent_support_union (p : T.decomposition.vertices) :
    (⋃ i : Bool × Bool, T.parentCoordinates (.inl (p, i)) ''
      (T.refinement.mesh (.inl (p, i))).toPlaneComplex.support) =
      ⋃ i, ((T.caps p).face i).carrier := by
  apply iUnion_congr
  intro i
  rw [(T.refinement.subdivision (.inl (p, i))).support, (T.caps p).carrier_eq i]
  rfl


theorem vertex_contribution_eq_cap_sum_of_interior
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) {q : S}
    (hq : q ∈ interior (⋃ i, ((T.caps p).face i).carrier)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      ∑ i : Bool × Bool, meshVertexAngleContribution g ((T.caps p).coordinates i)
        (T.refinement.mesh (.inl (p, i))) q := by
  rw [T.vertex_contribution_eq_parent_sum]
  symm
  apply Fintype.sum_of_injective (fun i : Bool × Bool => (Sum.inl (p, i) : T.Parent))
  · intro i j h
    simpa only [Sum.inl.injEq, Prod.mk.injEq, true_and] using h
  · intro i hi
    apply meshVertexAngleContribution_eq_zero_of_not_mem_support
    apply coordinate_mesh_family_not_mem_of_interior_subfamily
      T.refinement.mesh T.parentCoordinates T.refinement.face
      (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
      T.refinement.intersection_frontier (fun j : Bool × Bool => .inl (p, j)) i
      (fun j h => hi ⟨j, h.symm⟩)
    rwa [T.cap_parent_support_union]
  · intro i
    rfl



theorem cap_center_vertex_fan (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis (p : S) =
      2 * Real.pi := by
  rw [T.vertex_contribution_eq_cap_sum_of_interior g p (T.caps p).center_mem_interior_union]
  simpa only [Fintype.sum_prod_type] using T.cap_center_contribution g p



theorem cap_mem_interior_of_not_mem_chord (p : T.decomposition.vertices) {q : S}
    (hq : ∃ i, q ∈ ((T.caps p).face i).carrier)
    (hchord : ∀ i, q ∉ (((T.caps p).face i).boundary 0).map '' Icc (0 : ℝ) 1) :
    q ∈ interior (⋃ i, ((T.caps p).face i).carrier) := by
  by_contra hnot
  have hfront : q ∈ frontier (⋃ i, ((T.caps p).face i).carrier) :=
    ⟨subset_closure (mem_iUnion.mpr hq), hnot⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp ((T.caps p).frontier_union_subset_chords hfront)
  exact hchord i hi

set_option maxHeartbeats 800000 in


theorem canonical_vertex_fan_away_from_cap_chords
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : ∃ i, q.1 ∈ ((T.caps p).face i).carrier)
    (hchord : ∀ i, q.1 ∉ (((T.caps p).face i).boundary 0).map '' Icc (0 : ℝ) 1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  by_cases hc : q.1 = (p : S)
  · exact hc ▸ T.cap_center_vertex_fan g p
  have hfirst (i : Bool) : q.1 ≠ (T.caps p).firstOuterTip i := by
    intro heq
    apply hchord (i, true)
    refine ⟨0, by simp, ?_⟩
    rw [heq, (T.caps p).boundary_map]
    simp [ChartCircleArrangementVertexPatch.VertexCapFaces.firstOuterTip,
      affineChartSegment, Fin.succAbove]
  have hsecond (i : Bool) : q.1 ≠ (T.caps p).secondOuterTip i := by
    intro heq
    apply hchord (true, i)
    refine ⟨1, by simp, ?_⟩
    rw [heq, (T.caps p).boundary_map]
    simp [ChartCircleArrangementVertexPatch.VertexCapFaces.secondOuterTip,
      affineChartSegment, Fin.succAbove]
  rw [T.vertex_contribution_eq_cap_sum_of_interior g p
    (T.cap_mem_interior_of_not_mem_chord p hq hchord)]
  rw [T.cap_contribution_away_from_original_vertices g p q hq hc hfirst hsecond]
  rw [if_neg]
  rintro ⟨i, t, ht, hpoint⟩
  exact hchord i ⟨t, Ioo_subset_Icc_self ht, hpoint⟩

set_option maxHeartbeats 800000 in


theorem canonical_vertex_fan_in_cap_interior
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ interior (⋃ i, ((T.caps p).face i).carrier)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  apply T.canonical_vertex_fan_away_from_cap_chords g p q
    (mem_iUnion.mp (interior_subset hq))
  intro i hi
  exact ((T.caps p).chord_subset_frontier_union i hi).2 hq

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
