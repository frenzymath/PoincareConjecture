import PoincareConjecture.Proofs.M76.Rigidity.OriginalBoundaryMembership
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import Mathlib.Analysis.Convex.PathConnected










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in



theorem dualBlock_mapsTo_original_interior
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hsB : s ∉ (T.marked 1).faces) :
    let : Fintype T.ambient.faces := T.finite.fintype
    MapsTo (fun x => (T.inverse x : X))
      (T.ambient.barycentricDualBlock s).space (interior R) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  let N := T.ambient.barycentricDualBlock s
  let c := s.centroid ℝ id
  have hNK : N.space ⊆ T.ambient.space :=
    (SimplicialComplex.space_subset_of_le (T.ambient.barycentricDualBlock_le s)).trans
      T.ambient.barycentricSubdivision_isSubdivision.space_eq.subset
  have hcN : c ∈ N.space := N.vertices_subset_space
    (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.marked_le 2 hs))
  have hspace : N.space ∩ (T.marked 1).space = ∅ := by
    calc
      N.space ∩ (T.marked 1).space = ((T.marked 1).barycentricDualBlock s).space :=
        T.ambient.barycentricDualBlock_space_inter_subcomplex (T.marked 1) (T.marked_le 1) s
      _ = ∅ := (T.marked 1).barycentricDualBlock_space_eq_empty_of_not_face
        ((T.marked 2).nonempty_of_mem_faces hs) hsB
  have hstar : N.closedStar c = N :=
    T.ambient.barycentricDualBlock_closedStar_faceCentroid (T.marked_le 2 hs)
  have hcv : StarConvex ℝ c N.space := by
    have h := N.starConvex_closedFaceStar {c} (p := c) (by
      simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff])
    simpa only [N.closedFaceStar_singleton_eq_closedStar, hstar] using h
  have hgc : ContinuousOn (fun x => (T.inverse x : X)) N.space :=
    continuous_subtype_val.comp_continuousOn (T.inverse_continuous.mono hNK)
  have hconn := (hcv.isPathConnected hcN).isConnected.isPreconnected.image
    (fun x => (T.inverse x : X)) hgc
  have hcD : c ∈ (T.marked 2).space := (T.marked 2).convexHull_subset_space hs
    (s.centroid_mem_convexHull ((T.marked 2).nonempty_of_mem_faces hs))
  obtain ⟨hcParam, hjc⟩ := T.parameter_disk_point hcD
  have hcR : (T.inverse c : X) ∈ R := hjc ▸ T.disk_in_region hcParam
  have hcint : (T.inverse c : X) ∈ interior R := by
    apply (mem_interior_iff_notMem_frontier hcR).mpr
    intro hcB
    exact hspace.subset ⟨hcN, (T.inverse_mem_boundary_iff (hNK hcN)).mp hcB⟩
  have hdisjoint : Disjoint (frontier (interior R))
      ((fun x => (T.inverse x : X)) '' N.space) := by
    apply disjoint_left.mpr
    rintro _ hxB ⟨x, hx, rfl⟩
    exact hspace.subset ⟨hx, (T.inverse_mem_boundary_iff (hNK hx)).mp
      (frontier_interior_subset hxB)⟩
  have hsub := hconn.m76_subset_of_disjoint_frontier isOpen_interior hdisjoint
    ⟨T.inverse c, ⟨c, hcN, rfl⟩, hcint⟩
  exact fun x hx => hsub ⟨x, hx, rfl⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
