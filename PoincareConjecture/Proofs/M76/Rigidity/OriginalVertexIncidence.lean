import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBlocks
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBoundaryMembership
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import Mathlib.Analysis.Convex.PathConnected









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)



theorem vertexBlock_subset_ambient (p : (T.marked 2).vertices) :
    (T.vertexBlock p).space ⊆ T.ambient.space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  exact (SimplicialComplex.space_subset_of_le
    (T.ambient.barycentricDualBlock_le {p.val})).trans
      T.ambient.barycentricSubdivision_isSubdivision.space_eq.subset




theorem vertexBlock_subset_original_interior [T2Space X]
    (p : (T.marked 2).vertices) (hpfront : (T.inverse p : X) ∉ frontier R) :
    MapsTo (fun x => (T.inverse x : X)) (T.vertexBlock p).space (interior R) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  let N := T.vertexBlock p
  obtain ⟨_, hpN, hstar, _, _⟩ := T.vertexBlock_centered_chart p
  have hstar' : N.closedStar p = N := hstar
  have hpK : (p : T.index → ℝ × V3) ∈ T.ambient.vertices := T.marked_le 2 p.property
  have hspace : N.space ∩ (T.marked 1).space = ∅ := by
    have hnot : {p.val} ∉ (T.marked 1).faces := by
      intro hp
      exact hpfront ((T.inverse_mem_boundary_iff
        (T.ambient.vertices_subset_space hpK)).mpr
          ((T.marked 1).vertices_subset_space hp))
    calc
      N.space ∩ (T.marked 1).space =
          ((T.marked 1).barycentricDualBlock {p.val}).space :=
        T.ambient.barycentricDualBlock_space_inter_subcomplex
          (T.marked 1) (T.marked_le 1) {p.val}
      _ = ∅ := (T.marked 1).barycentricDualBlock_space_eq_empty_of_not_face
        (Finset.singleton_nonempty _) hnot
  have hconv : StarConvex ℝ (p : T.index → ℝ × V3) N.space := by
    have h := N.starConvex_closedFaceStar {p.val} (p := p.val) (by
      simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff])
    simpa only [N.closedFaceStar_singleton_eq_closedStar, hstar'] using h
  have hpS : (p : T.index → ℝ × V3) ∈ N.space := N.vertices_subset_space hpN
  have hgc : ContinuousOn (fun x => (T.inverse x : X)) N.space :=
    continuous_subtype_val.comp_continuousOn
      (T.inverse_continuous.mono (T.vertexBlock_subset_ambient p))
  have hconn := (hconv.isPathConnected hpS).isConnected.isPreconnected.image
    (fun x => (T.inverse x : X)) hgc
  have hpD : (T.inverse p : X) ∈ j '' closedBall (0 : V2) 1 :=
    (T.inverse_mem_disk_iff (T.ambient.vertices_subset_space hpK)).mpr
      ((T.marked 2).vertices_subset_space p.property)
  have hpR : (T.inverse p : X) ∈ R := by
    obtain ⟨z, hz, hzp⟩ := hpD
    exact hzp ▸ T.disk_in_region hz
  have hpint : (T.inverse p : X) ∈ interior R := by
    by_contra hnot
    exact hpfront ⟨subset_closure hpR, hnot⟩
  have hdisjoint : Disjoint (frontier (interior R))
      ((fun x => (T.inverse x : X)) '' N.space) := by
    apply Set.disjoint_left.mpr
    rintro _ hxfront ⟨x, hx, rfl⟩
    exact hspace.subset ⟨hx, (T.inverse_mem_boundary_iff
      (T.vertexBlock_subset_ambient p hx)).mp (frontier_interior_subset hxfront)⟩
  have hsub := hconn.m76_subset_of_disjoint_frontier isOpen_interior hdisjoint
    ⟨T.inverse p, ⟨p, hpS, rfl⟩, hpint⟩
  exact fun x hx => hsub ⟨x, hx, rfl⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
