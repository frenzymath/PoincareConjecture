import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.VertexCaps

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)

omit [T2Space M] in

theorem center_mem_interior_union : p ∈ interior (⋃ i, (B.face i).carrier) :=
  mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
    (B.isOpen_neighborhood.mem_nhds B.mem_neighborhood) B.neighborhood_subset_carriers)

theorem first_boundary_mem_interior_union (i : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((B.face i).boundary 2).map t ∈ interior (⋃ j, (B.face j).carrier) := by
  let j : Bool × Bool := (i.1, !i.2)
  have hij : i ≠ j := by
    intro h
    have h' := congrArg Prod.snd h
    simp [j] at h'
  have hinter : (B.face i).carrier ∩ (B.face j).carrier ⊆ frontier (B.face i).carrier := by
    rw [(B.intersections hij).1 rfl, ← B.first_image i]
    exact (B.face i).boundary_image_subset_frontier 2
  have h := mem_interior_union_of_coordinate_triangles_shared_edge
    (B.face i) (B.face j) (B.coordinates i) (B.coordinates j)
    (rightTriangleBasis B.scale_pos) (rightTriangleBasis B.scale_pos)
    (B.triangle_subset_source i) (B.triangle_subset_source j)
    (B.carrier_eq i) (B.carrier_eq j) (B.boundary_map i) (B.boundary_map j)
    hinter 2 2 (B.boundary_injective i 2) (B.first_boundary_agreement rfl) ht
  exact interior_mono (union_subset (subset_iUnion _ i) (subset_iUnion _ j)) h

theorem second_boundary_mem_interior_union (i : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((B.face i).boundary 1).map t ∈ interior (⋃ j, (B.face j).carrier) := by
  let j : Bool × Bool := (!i.1, i.2)
  have hij : i ≠ j := by
    intro h
    have h' := congrArg Prod.fst h
    simp [j] at h'
  have hinter : (B.face i).carrier ∩ (B.face j).carrier ⊆ frontier (B.face i).carrier := by
    rw [(B.intersections hij).2.1 rfl, ← B.second_image i]
    exact (B.face i).boundary_image_subset_frontier 1
  have h := mem_interior_union_of_coordinate_triangles_shared_edge
    (B.face i) (B.face j) (B.coordinates i) (B.coordinates j)
    (rightTriangleBasis B.scale_pos) (rightTriangleBasis B.scale_pos)
    (B.triangle_subset_source i) (B.triangle_subset_source j)
    (B.carrier_eq i) (B.carrier_eq j) (B.boundary_map i) (B.boundary_map j)
    hinter 1 1 (B.boundary_injective i 1) (B.second_boundary_agreement rfl) ht
  exact interior_mono (union_subset (subset_iUnion _ i) (subset_iUnion _ j)) h

omit [T2Space M] in
private theorem second_boundary_end_eq_chord_end (i : Bool × Bool) :
    ((B.face i).boundary 1).map 1 = ((B.face i).boundary 0).map 1 := by
  rw [B.boundary_map i 1, B.boundary_map i 0]
  simp [affineChartSegment, Fin.succAbove]

omit [T2Space M] in
private theorem first_boundary_end_eq_chord_start (i : Bool × Bool) :
    ((B.face i).boundary 2).map 1 = ((B.face i).boundary 0).map 0 := by
  rw [B.boundary_map i 2, B.boundary_map i 0]
  simp [affineChartSegment, Fin.succAbove, Fin.lt_def]

theorem frontier_union_subset_chords :
    frontier (⋃ i, (B.face i).carrier) ⊆
      ⋃ i, ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  have hclosed : IsClosed (⋃ i, (B.face i).carrier) :=
    isClosed_iUnion_of_finite (fun i => (B.face i).isClosed_carrier)
  intro q hq
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hclosed.frontier_subset hq)
  have hqfront : q ∈ frontier (B.face i).carrier := by
    refine ⟨subset_closure hi, ?_⟩
    intro h
    exact hq.2 (interior_mono (subset_iUnion (fun j => (B.face j).carrier) i) h)
  rw [(B.face i).boundary_carrier] at hqfront
  obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp hqfront
  fin_cases k
  · exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
  · by_cases hzero : t = 0
    · subst t
      have heq : ((B.face i).boundary 1).map 0 = p := by
        rw [B.second_map i 0 (by simp)]
        simpa [Prod.zero_eq_mk] using P.sectorCoordinates_zero i
      exact False.elim (hq.2 (heq.symm ▸ B.center_mem_interior_union))
    by_cases hone : t = 1
    · subst t
      exact mem_iUnion.mpr ⟨i, 1, by simp, (B.second_boundary_end_eq_chord_end i).symm⟩
    exact False.elim (hq.2 (B.second_boundary_mem_interior_union i
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩))
  · by_cases hzero : t = 0
    · subst t
      have heq : ((B.face i).boundary 2).map 0 = p := by
        rw [B.first_map i 0 (by simp)]
        simpa [Prod.zero_eq_mk] using P.sectorCoordinates_zero i
      exact False.elim (hq.2 (heq.symm ▸ B.center_mem_interior_union))
    by_cases hone : t = 1
    · subst t
      exact mem_iUnion.mpr ⟨i, 0, by simp, (B.first_boundary_end_eq_chord_start i).symm⟩
    exact False.elim (hq.2 (B.first_boundary_mem_interior_union i
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩))

end ChartCircleArrangementVertexPatch.VertexCapFaces
end PoincareConjecture.Topology.Surface
