import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointFaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.EdgeGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

variable {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem m64Intrinsic_band_endpoint_contact_corner
    (right : Bool) (p : Fin B.interface.count × Bool)
    (hp : p ≠ if right then (B.lastCell, false) else (B.firstCell, true)) :
    ((B.endpointEdge right).map '' Icc (0 : ℝ) 1) ∩ (B.face p).carrier ⊆
      range (fun k : Fin 3 => B.faceCoordinates p (B.faceBasis p k)) := by
  rintro x hx
  have heq := mem_singleton_iff.mp (m64Intrinsic_band_endpoint_inter_other_face B right p hp hx)
  have htip : (B.endpointEdge right).map (if right then 1 else 0) =
      B.vertex (if right then (Fin.last B.interface.count, true) else (0, false)) := by
    cases right
    · rw [B.endpointEdge_map]
      change B.coordinates (collarParameterEquiv.symm (0, 0 * B.height 0)) = _
      simp only [ObliqueBandFaces.vertex, Bool.false_eq_true, ↓reduceIte,
        B.cut_first, zero_mul]
    · rw [B.endpointEdge_map]
      change B.coordinates (collarParameterEquiv.symm (1, 1 * B.height 1)) = _
      simp only [ObliqueBandFaces.vertex, ↓reduceIte, B.cut_last,
        B.interface.height_last, B.height_one, one_mul]
  have hxv := heq.trans htip
  obtain ⟨k, hk⟩ := (B.vertex_mem_face_carrier_iff p _).mp (hxv ▸ hx.2)
  exact ⟨k, hk.trans hxv.symm⟩

theorem m64Intrinsic_band_side_endpoint_contact_corners
    (right : Bool) (p : Fin B.interface.count × Bool) (k : Fin 3)
    (hnot : ¬(p = (if right then (B.lastCell, false) else (B.firstCell, true)) ∧
      k = (if right then 0 else 2))) :
    (((B.face p).boundary k).map '' Icc (0 : ℝ) 1) ∩
        ((B.endpointEdge right).map '' Icc (0 : ℝ) 1) ⊆
      range (fun j : Fin 3 => B.faceCoordinates p (B.faceBasis p j)) := by
  rintro x hx
  by_cases hp : p = if right then (B.lastCell, false) else (B.firstCell, true)
  · have hk : k ≠ if right then 0 else 2 := fun h => hnot ⟨hp, h⟩
    have hedge : ((B.face p).boundary (if right then 0 else 2)).map '' Icc (0 : ℝ) 1 =
        (B.endpointEdge right).map '' Icc (0 : ℝ) 1 := by
      subst p
      cases right <;> rfl
    have hboth : x ∈
        ((B.faceCoordinates p ∘ affineChartSegment
          (B.faceBasis p (k.succAbove 0)) (B.faceBasis p (k.succAbove 1))) '' Icc (0 : ℝ) 1) ∩
        ((B.faceCoordinates p ∘ affineChartSegment
          (B.faceBasis p ((if right then (0 : Fin 3) else 2).succAbove 0))
          (B.faceBasis p ((if right then (0 : Fin 3) else 2).succAbove 1))) '' Icc (0 : ℝ) 1) := by
      simpa only [← B.face_boundary_image p k, ← B.face_boundary_image p (if right then 0 else 2),
        hedge] using hx
    have hv := Euler.coordinate_distinct_edges (B.faceCoordinates p) (B.faceBasis p)
      (B.face_triangle_subset_source p) k (if right then 0 else 2) hk hboth
    rcases hv with hv | hv
    · exact ⟨k.succAbove 0, hv.symm⟩
    · exact ⟨k.succAbove 1, (mem_singleton_iff.mp hv).symm⟩
  · apply m64Intrinsic_band_endpoint_contact_corner B right p hp
    exact ⟨hx.2, (B.face p).isClosed_carrier.frontier_subset
      ((B.face p).boundary_image_subset_frontier k hx.1)⟩

theorem m64Intrinsic_band_side_outer_contact_corners
    (p : Fin B.interface.count × Bool) (k : Fin 3)
    (hnot : ∀ right : Bool,
      ¬(p = (if right then (B.lastCell, false) else (B.firstCell, true)) ∧
        k = (if right then 0 else 2))) :
    (((B.face p).boundary k).map '' Icc (0 : ℝ) 1) ∩ (B.leftCut ∪ B.rightCut) ⊆
      range (fun j : Fin 3 => B.faceCoordinates p (B.faceBasis p j)) := by
  rintro x ⟨hxside, hxcut⟩
  rcases hxcut with hxleft | hxright
  · apply m64Intrinsic_band_side_endpoint_contact_corners B false p k (hnot false)
    exact ⟨hxside, by
      simpa only [B.endpointEdge_image, Bool.false_eq_true, ↓reduceIte] using hxleft⟩
  · apply m64Intrinsic_band_side_endpoint_contact_corners B true p k (hnot true)
    exact ⟨hxside, by simpa only [B.endpointEdge_image, ↓reduceIte] using hxright⟩

end PoincareConjecture
