import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBlocks
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

theorem HamiltonProperDiskTriangulation.vertexBlock_subset_interior
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (hpfront : (p : E) ∉ frontier R) :
    (T.vertexBlock p).space ⊆ interior R := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  let N := T.vertexBlock p
  obtain ⟨_, hpN, hstar, hsource, _⟩ := T.vertexBlock_centered_chart p
  have hspace : N.space ∩ frontier R = ∅ := by
    have hnot : {(p : E)} ∉ T.boundary.faces := by
      intro hp
      exact hpfront (T.boundary_space.subset (T.boundary.vertices_subset_space hp))
    calc
      N.space ∩ frontier R = N.space ∩ T.boundary.space :=
        congrArg (fun S => N.space ∩ S) T.boundary_space.symm
      _ = (T.boundary.barycentricDualBlock {(p : E)}).space :=
        T.ambient.barycentricDualBlock_space_inter_subcomplex
          T.boundary T.boundary_le {(p : E)}
      _ = ∅ := T.boundary.barycentricDualBlock_space_eq_empty_of_not_face
        (Finset.singleton_nonempty _) hnot
  have hfaceStar : N.closedFaceStar {(p : E)} = N.closedStar p := by
    ext s
    change (s ∈ N.faces ∧ {(p : E)} ∪ s ∈ N.faces) ↔
      (s ∈ N.faces ∧ insert (p : E) s ∈ N.faces)
    rw [Finset.singleton_union]
  have hconv : StarConvex ℝ (p : E) N.space := by
    have hstarN : N.closedStar p = N := hstar
    have h := N.starConvex_closedFaceStar {(p : E)} (p := (p : E)) (by
      simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff])
    simpa only [hfaceStar, hstarN] using h
  have hpS : (p : E) ∈ N.space := N.vertices_subset_space hpN
  have hpSource := hsource hpS
  have hpD := T.disk_space.subset (T.disk.vertices_subset_space p.property)
  have hpR : (p : E) ∈ R := by
    rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hregion, hdisk⟩
    · exact interior_subset (hinside hpSource)
    · exact (hregion p hpSource).mpr ((hdisk p hpSource).mp hpD).1
  have hpint : (p : E) ∈ interior R := by
    by_contra hnot
    exact hpfront ⟨subset_closure hpR, hnot⟩
  apply (hconv.isPathConnected hpS).isConnected.isPreconnected.m76_subset_of_disjoint_frontier
    isOpen_interior
  · apply Set.disjoint_left.mpr
    intro x hxfront hxN
    exact hspace.subset ⟨hxN, frontier_interior_subset hxfront⟩
  · exact ⟨p, hpS, hpint⟩

end PoincareConjecture.M76.HamiltonIndexOne
