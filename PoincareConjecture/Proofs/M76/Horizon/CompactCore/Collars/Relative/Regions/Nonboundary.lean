import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.Heights
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue








set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (T : CoorientedSurfaceStars E)

open Classical in


theorem nonboundary_dual_inter_boundary {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hsB : s ∉ (T.marked 1).faces) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ∩ (T.marked 1).space = ∅ := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  change (T.ambient.barycentricDualBlock s).space ∩ (T.marked 1).space = ∅
  rw [T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 1) (T.marked_le 1) s]
  exact (T.marked 1).barycentricDualBlock_space_eq_empty_of_not_face
    ((T.marked 2).nonempty_of_mem_faces hs) hsB

open Classical in


theorem nonboundary_dual_subset_region {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hsB : s ∉ (T.marked 1).faces) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ⊆ (T.marked 0).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  change (T.ambient.barycentricDualBlock s).space ⊆ (T.marked 0).space
  let N := T.ambient.barycentricDualBlock s
  let c := s.centroid ℝ id
  obtain ⟨p0, hp0⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let p : (T.marked 2).vertices := ⟨p0, (T.marked 2).face_subset_vertices hs hp0⟩
  have hps : (p : E) ∈ s := hp0
  have hNS := T.dualBlock_subset_star p hps
  rcases T.chart_model p with hinside | hhalf
  · exact hNS.trans hinside.1
  · let a : E → ℝ := fun x => (T.chart p x).1.1
    have ha : ContinuousOn a N.space :=
      (((T.star_affine p).continuousOn (finite_closedStar_faces T.finite p)).fst.fst).mono hNS
    have hcN : c ∈ N.space := N.vertices_subset_space
      (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.marked_le 2 hs))
    have hstar : N.closedStar c = N :=
      T.ambient.barycentricDualBlock_closedStar_faceCentroid (T.marked_le 2 hs)
    have hcv : StarConvex ℝ c N.space := by
      have h := N.starConvex_closedFaceStar {c} (p := c) (by
        simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff])
      simpa only [closedFaceStar_singleton_eq_closedStar, hstar] using h
    have hconn := (hcv.isPathConnected hcN).isConnected.isPreconnected
    have hzero : ∀ x ∈ N.space, a x ≠ 0 := by
      intro x hx he
      exact (T.nonboundary_dual_inter_boundary hs hsB).subset
        ⟨hx, (hhalf.2 x (hNS hx)).mpr he⟩
    have hcS : c ∈ (T.marked 2).space := (T.marked 2).convexHull_subset_space hs
      (s.centroid_mem_convexHull ((T.marked 2).nonempty_of_mem_faces hs))
    have hcpos : 0 ≤ a c := (hhalf.1 c (hNS hcN)).mp (T.surface_subset_region hcS)
    intro x hx
    apply (hhalf.1 x (hNS hx)).mpr
    by_contra hn
    have hxneg : a x < 0 := lt_of_not_ge hn
    obtain ⟨z, hz, haz⟩ := hconn.intermediate_value hx hcN ha ⟨hxneg.le, hcpos⟩
    exact hzero z hz haz

open Classical in


theorem dualRegion_eq_dualBlock_of_not_boundary {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hsB : s ∉ (T.marked 1).faces) :
    let : Fintype T.ambient.faces := T.finite.fintype
    T.dualRegion s = (T.ambient.barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  exact inter_eq_left.mpr (T.nonboundary_dual_subset_region hs hsB)

open Classical in

theorem dualRegionRim_eq_link_of_not_boundary {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hsB : s ∉ (T.marked 1).faces) :
    let : Fintype T.ambient.faces := T.finite.fintype
    T.dualRegionRim s =
      ((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.ambient.barycentricDualBlock s
  have hlink : (N.link (s.centroid ℝ id)).space ⊆ N.space :=
    space_subset_of_le (fun _ ht => ht.1)
  change ((N.link (s.centroid ℝ id)).space ∩ (T.marked 0).space) ∪
    (N.space ∩ (T.marked 1).space) = _
  rw [inter_eq_left.mpr (hlink.trans (T.nonboundary_dual_subset_region hs hsB)),
    T.nonboundary_dual_inter_boundary hs hsB, union_empty]

end Geometry.SimplicialComplex.CoorientedSurfaceStars
