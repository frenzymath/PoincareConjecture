import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapFaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Gluing













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem segment_mem_triangle (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (i : Fin 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t ∈
      convexHull ℝ (range b) := by
  apply segment_subset_convexHull (mem_range_self (i.succAbove 0))
    (mem_range_self (i.succAbove 1))
  rw [← affineSegment_eq_segment]
  refine ⟨t, ht, ?_⟩
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]





theorem m64Intrinsic_coordinate_face_boundary_injective
    (face : SmoothFace AnnulusCoordinates)
    (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : convexHull ℝ (range b) ⊆ C.source)
    (hboundary : ∀ k : Fin 3, (face.boundary k).map = C ∘
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) (k : Fin 3) :
    InjOn (face.boundary k).map (Icc (0 : ℝ) 1) := by
  have hne : b (k.succAbove 1) - b (k.succAbove 0) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have h := Fin.succAbove_right_injective (p := k) (b.ind.injective heq)
    norm_num at h
  intro t ht s hs heq
  rw [hboundary] at heq
  have h := C.injOn (hsource (segment_mem_triangle b k ht))
    (hsource (segment_mem_triangle b k hs)) heq
  exact smul_left_injective ℝ hne (add_left_cancel h)





theorem m64Intrinsic_cap_band_attachment_interior
    (face : SmoothFace AnnulusCoordinates)
    (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (basis : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : convexHull ℝ (range basis) ⊆ C.source)
    (hcarrier : face.carrier = C '' convexHull ℝ (range basis))
    (hboundary : ∀ k : Fin 3, (face.boundary k).map = C ∘
      affineChartSegment (basis (k.succAbove 0)) (basis (k.succAbove 1)))
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (k : Fin 3) (right : Bool) {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hpoint : (face.boundary k).map t = (B.endpointEdge right).map u)
    (hshared : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      (face.boundary k).map '' Icc (0 : ℝ) 1)
    (hinter : face.carrier ∩ B.carrier ⊆ frontier face.carrier) :
    (face.boundary k).map t ∈ interior (face.carrier ∪ B.carrier) := by
  let other := ⋃ j : {j : Fin 3 // j ≠ k}, (face.boundary j).map '' Icc (0 : ℝ) 1
  have hother : IsCompact other := isCompact_iUnion (fun j =>
    isCompact_Icc.image_of_continuousOn (face.boundary j).smooth.continuousOn)
  have hnot : (face.boundary k).map t ∉ other := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact coordinate_triangle_boundary_avoids_other_edges face C basis hsource hboundary
      (Ne.symm j.property) ht hj
  obtain ⟨N, hN, huN, hfrontN⟩ := B.exists_endpoint_frontier_neighborhood right hu
  have hregular : closure (interior face.carrier) = face.carrier := by
    rw [hcarrier]
    exact coordinate_triangle_closure_interior C basis hsource
  have hdisjoint : Disjoint (interior face.carrier) (interior B.carrier) := by
    apply disjoint_left.mpr
    intro z hz hzB
    exact disjoint_left.mp disjoint_interior_frontier hz
      (hinter ⟨interior_subset hz, interior_subset hzB⟩)
  apply (face.boundary k).mem_interior_union_of_local_frontiers (0 : AnnulusCoordinates)
    (m64Intrinsic_coordinate_face_boundary_injective face C basis hsource hboundary k)
    (by intro z _; simp) (face.interior_boundary_image k)
    face.isClosed_carrier B.isClosed_carrier hregular B.closure_interior_carrier hdisjoint ht
    (face.isClosed_carrier.frontier_subset
      (face.boundary_image_subset_frontier k ⟨t, Ioo_subset_Icc_self ht, rfl⟩))
    (hpoint ▸ B.isClosed_carrier.frontier_subset
      (B.endpointEdge_subset_frontier right ⟨u, Ioo_subset_Icc_self hu, rfl⟩))
    ((hother.isClosed.isOpen_compl.inter hN).mem_nhds ⟨hnot, hpoint ▸ huN⟩)
  · rintro q ⟨hqN, hqfront⟩
    rw [face.boundary_carrier] at hqfront
    obtain ⟨j, hj⟩ := mem_iUnion.mp hqfront
    by_cases hjk : j = k
    · simpa only [hjk] using hj
    · exact False.elim (hqN.1 (mem_iUnion.mpr ⟨⟨j, hjk⟩, hj⟩))
  · exact fun q hq => hshared (hfrontN ⟨hq.1.2, hq.2⟩)

end PoincareConjecture
