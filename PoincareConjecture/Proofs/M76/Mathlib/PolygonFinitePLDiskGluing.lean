import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLTriangleFilling
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitBoundaryMembership
import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskPartition
import PoincareConjecture.Proofs.M76.Mathlib.SegmentParameterMembership
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGluing
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangulation

set_option autoImplicit false

open Set TriangleDiskModel

namespace Polygon

theorem isFinitePLBallPair_of_split {m n : ℕ} (u : Fin (m + 2) → ℝ × ℝ)
    (v : Fin (n + 2) → ℝ × ℝ)
    (hP : (mk (Fin.append u v)).HasSimplicialEdges)
    (hinj : Function.Injective (Fin.append u v))
    (hd : openSegment ℝ (u 0) (v 0) ⊆ (mk (Fin.append u v)).inside)
    (hQ : IsFinitePLBallPair (ℝ × ℝ) (closure (mk (Fin.snoc u (v 0))).inside)
      ((mk (Fin.snoc u (v 0))).boundary ℝ))
    (hR : IsFinitePLBallPair (ℝ × ℝ) (closure (mk (Fin.snoc v (u 0))).inside)
      ((mk (Fin.snoc v (u 0))).boundary ℝ)) :
    IsFinitePLBallPair (ℝ × ℝ) (closure (mk (Fin.append u v)).inside)
      ((mk (Fin.append u v)).boundary ℝ) := by
  let P := mk (Fin.append u v)
  let Q := mk (Fin.snoc u (v 0))
  let R := mk (Fin.snoc v (u 0))
  have hchord : segment ℝ (u 0) (v 0) ∩ P.boundary ℝ ⊆ {u 0, v 0} := by
    rintro x ⟨hx, hxb⟩
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with rfl | rfl | hx
    · simp
    · simp
    · exact ((hd hx).1 hxb).elim
  obtain ⟨hsQ, hsR⟩ := hasSimplicialEdges_split u v hP hinj hchord
  obtain ⟨hiQ, hiR⟩ := injective_split u v hinj
  obtain ⟨_, hcover, hinter⟩ := region_partition_split u v hP hinj hd
  obtain ⟨e, hePL, heb, hep⟩ := Q.exists_finitePL_triangle_filling hsQ hiQ hQ
    rightTriangle independent_rightTriangle
  obtain ⟨f, hfPL, hfb, hfp⟩ := R.exists_finitePL_triangle_filling hsR hiR hR
    leftTriangle independent_leftTriangle
  have hep' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hx : AffineMap.lineMap (v 0) (u 0) t ∈ closure Q.inside) :
      (e ⟨AffineMap.lineMap (v 0) (u 0) t, hx⟩ : ℝ × ℝ) =
        AffineMap.lineMap (0, 1) (0, 0) t := by
    simpa [Q, rightTriangle] using
      hep t ht (by simpa only [Q, Fin.snoc_last, Fin.snoc_apply_zero] using hx)
  have hfp' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hx : AffineMap.lineMap (v 0) (u 0) t ∈ closure R.inside) :
      (f ⟨AffineMap.lineMap (v 0) (u 0) t, hx⟩ : ℝ × ℝ) =
        AffineMap.lineMap (0, 1) (0, 0) t := by
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa [R, leftTriangle, AffineMap.lineMap_apply_one_sub] using
      hfp (1 - t) ht' (by
        simpa only [R, Fin.snoc_last, Fin.snoc_apply_zero,
          AffineMap.lineMap_apply_one_sub] using hx)
  have hdiagQ : segment ℝ (v 0) (u 0) ⊆ closure Q.inside := by
    rw [segment_symm, ← hinter]
    exact inter_subset_left
  have hdiagR : segment ℝ (v 0) (u 0) ⊆ closure R.inside := by
    rw [segment_symm, ← hinter]
    exact inter_subset_right
  have hei : Function.Injective (fun x => (e x : ℝ × ℝ)) := Subtype.val_injective.comp e.injective
  have hfi : Function.Injective (fun x => (f x : ℝ × ℝ)) := Subtype.val_injective.comp f.injective
  have hoverlap (x : closure Q.inside) :
      (x : ℝ × ℝ) ∈ closure R.inside ↔ (e x : ℝ × ℝ) ∈ convexHull ℝ (range leftTriangle) := by
    have hs : (x : ℝ × ℝ) ∈ closure R.inside ↔ (x : ℝ × ℝ) ∈ segment ℝ (v 0) (u 0) := by
      rw [segment_symm, ← hinter]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
    have ht : (e x : ℝ × ℝ) ∈ convexHull ℝ (range leftTriangle) ↔
        (e x : ℝ × ℝ) ∈ segment ℝ (0, 1) (0, 0) := by
      rw [← region_inter]
      simp only [mem_inter_iff, (e x).property, true_and]
    exact hs.trans ((hei.segment_mem_iff_of_lineMap hdiagQ hep' x).trans ht.symm)
  have hagree (x : ℝ × ℝ) (hxQ : x ∈ closure Q.inside) (hxR : x ∈ closure R.inside) :
      (e ⟨x, hxQ⟩ : ℝ × ℝ) = f ⟨x, hxR⟩ := by
    have hx : x ∈ segment ℝ (v 0) (u 0) := by
      rw [segment_symm, ← hinter]
      exact ⟨hxQ, hxR⟩
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact (hep' t ht hxQ).trans (hfp' t ht hxR).symm
  have htri : ∃ K, P.IsTriangulation K := by
    cases n <;> exact P.exists_triangulation hP hinj
  obtain ⟨K, hK⟩ := htri
  obtain ⟨H, hHPL, hHe, hHf⟩ := Homeomorph.exists_union_of_isFinitePL e f hePL hfPL
    K hK.finite_faces (hK.space_eq.trans hcover) hoverlap hagree
  let G := (Homeomorph.setCongr hcover).trans (H.trans (Homeomorph.setCongr region_union))
  have hGPL : G.IsFinitePL := hHPL.setCongr hcover.symm region_union
  have hGe (x : closure P.inside) (hx : (x : ℝ × ℝ) ∈ closure Q.inside) :
      (G x : ℝ × ℝ) = e ⟨x, hx⟩ := hHe ⟨x, hx⟩
  have hGf (x : closure P.inside) (hx : (x : ℝ × ℝ) ∈ closure R.inside) :
      (G x : ℝ × ℝ) = f ⟨x, hx⟩ := hHf ⟨x, hx⟩
  have hboundary (x : closure P.inside) : (x : ℝ × ℝ) ∈ P.boundary ℝ ↔
      (G x : ℝ × ℝ) ∈ frontier (convexHull ℝ (range wholeTriangle)) := by
    have hx : (x : ℝ × ℝ) ∈ closure Q.inside ∪ closure R.inside := hcover ▸ x.property
    rcases hx with hxQ | hxR
    · have ho : (x : ℝ × ℝ) ∈ openSegment ℝ (u 0) (v 0) ↔
          (e ⟨x, hxQ⟩ : ℝ × ℝ) ∈ openSegment ℝ (0, 1) (0, 0) := by
        simpa only [openSegment_symm ℝ (v 0) (u 0)] using
          hei.openSegment_mem_iff_of_lineMap hdiagQ hep' ⟨x, hxQ⟩
      rw [hGe x hxQ]
      exact ((boundary_membership_split u v hP hinj hd).1 x hxQ).trans
        ((and_congr (heb ⟨x, hxQ⟩) (not_congr ho)).trans
          ((frontier_membership.1 (e ⟨x, hxQ⟩) (e ⟨x, hxQ⟩).property).symm))
    · have ho : (x : ℝ × ℝ) ∈ openSegment ℝ (u 0) (v 0) ↔
          (f ⟨x, hxR⟩ : ℝ × ℝ) ∈ openSegment ℝ (0, 1) (0, 0) := by
        simpa only [openSegment_symm ℝ (v 0) (u 0)] using
          hfi.openSegment_mem_iff_of_lineMap hdiagR hfp' ⟨x, hxR⟩
      rw [hGf x hxR]
      exact ((boundary_membership_split u v hP hinj hd).2 x hxR).trans
        ((and_congr (hfb ⟨x, hxR⟩) (not_congr ho)).trans
          ((frontier_membership.2 (f ⟨x, hxR⟩) (f ⟨x, hxR⟩).property).symm))
  have hbP : P.boundary ℝ ⊆ closure P.inside := by
    have hfP : frontier P.inside = P.boundary ℝ := by
      cases n <;> exact frontier_inside _ hP hinj
    rw [← hfP]
    exact frontier_subset_closure
  have htarget := wholeTriangle.isFinitePLBallPair_convexHull_triangle independent_wholeTriangle
  exact htarget.of_homeomorph hbP G hGPL hboundary

end Polygon
