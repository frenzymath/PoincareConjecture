import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointFaces

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem band_faces_compatible_of_intersection
    {F G : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo lo' : ℝ → ℝ} {a b ua wa ub wb ra rb a' b' ua' wa' ub' wb' ra' rb' : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (B' : ObliqueBandFaces G lo' a' b' ua' wa' ub' wb' ra' rb')
    (i : Fin B.interface.count × Bool) (j : Fin B'.interface.count × Bool)
    (hinter : (∃ k l : Fin 3, (B.face i).carrier ∩ (B'.face j).carrier =
        ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 =
        ((B'.face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ q : AnnulusCoordinates, (B.face i).carrier ∩ (B'.face j).carrier ⊆ {q}) :
    CoordinateTriangleBoundaryIntersection (B.faceCoordinates i) (B'.faceCoordinates j)
      (B.faceBasis i) (B'.faceBasis j) := by
  rcases hinter with ⟨k, l, hk, hl⟩ | ⟨q, hq⟩
  · apply CoordinateTriangleBoundaryIntersection.subsegment k l 0 1 0 1
      (by simp) (by simp) (by simp) (by simp)
    · simpa only [uIcc_of_le zero_le_one, ← B.face_carrier_eq_coordinates i,
        ← B'.face_carrier_eq_coordinates j] using hk.trans (B.face_boundary_image i k)
    · simpa only [uIcc_of_le zero_le_one, ← B.face_carrier_eq_coordinates i,
        ← B'.face_carrier_eq_coordinates j] using
        hk.trans (hl.trans (B'.face_boundary_image j l))
  · by_cases hne : ((B.face i).carrier ∩ (B'.face j).carrier).Nonempty
    · have hdisjoint : Disjoint (interior (B.face i).carrier) (interior (B'.face j).carrier) := by
        apply disjoint_left.mpr
        intro z hi hj
        have hzi : z ∈ interior ((B.face i).carrier ∩ (B'.face j).carrier) := by
          rw [interior_inter]
          exact ⟨hi, hj⟩
        have h := interior_mono hq hzi
        simp only [interior_singleton, notMem_empty] at h
      have hreg : closure (interior (B.face i).carrier) = (B.face i).carrier := by
        rw [B.face_carrier_eq_coordinates]
        exact coordinate_triangle_closure_interior (B.faceCoordinates i) (B.faceBasis i)
          (B.face_triangle_subset_source i)
      have hreg' : closure (interior (B'.face j).carrier) = (B'.face j).carrier := by
        rw [B'.face_carrier_eq_coordinates]
        exact coordinate_triangle_closure_interior (B'.faceCoordinates j) (B'.faceBasis j)
          (B'.face_triangle_subset_source j)
      have hleft := hdisjoint.closure_right isOpen_interior
      have hright := hdisjoint.symm.closure_right isOpen_interior
      rw [hreg'] at hleft
      rw [hreg] at hright
      obtain ⟨z, hz⟩ := hne
      have hzq : z = q := mem_singleton_iff.mp (hq hz)
      have hqfront : q ∈ frontier (B.face i).carrier ∩ frontier (B'.face j).carrier := by
        rw [← hzq]
        exact ⟨⟨subset_closure hz.1, fun hi => disjoint_left.mp hleft hi hz.2⟩,
          ⟨subset_closure hz.2, fun hj => disjoint_left.mp hright hj hz.1⟩⟩
      apply CoordinateTriangleBoundaryIntersection.point q
      · rw [← B.face_frontier_eq_coordinates]
        exact hqfront.1
      · rw [← B'.face_frontier_eq_coordinates]
        exact hqfront.2
      · rwa [← B.face_carrier_eq_coordinates, ← B'.face_carrier_eq_coordinates]
    · apply CoordinateTriangleBoundaryIntersection.disjoint
      rw [← B.face_carrier_eq_coordinates, ← B'.face_carrier_eq_coordinates]
      exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)

theorem m64Intrinsic_band_faces_canonical_compatibility
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (i j : Fin B.interface.count × Bool) (hij : i ≠ j) :
    CoordinateTriangleBoundaryIntersection (B.faceCoordinates i) (B.faceCoordinates j)
      (B.faceBasis i) (B.faceBasis j) := by
  apply band_faces_compatible_of_intersection B B i j
  rcases B.face_intersection i j hij with ⟨k, l, hedge, hinter⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨k, l, hinter, congrArg (fun e => e.map '' Icc (0 : ℝ) 1) hedge⟩
  · exact Or.inr ⟨B.vertex v, hv⟩

theorem m64Intrinsic_shared_cut_bands_canonical_compatibility
    {F G : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo lo' : ℝ → ℝ} {a b ua wa ub wb ra rb a' b' ua' wa' ub' wb' ra' rb' : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (B' : ObliqueBandFaces G lo' a' b' ua' wa' ub' wb' ra' rb')
    (right right' : Bool)
    (hinter : B.carrier ∩ B'.carrier = (B.endpointEdge right).map '' Icc (0 : ℝ) 1)
    (hshared : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 =
      (B'.endpointEdge right').map '' Icc (0 : ℝ) 1)
    (i : Fin B.interface.count × Bool) (j : Fin B'.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection (B.faceCoordinates i) (B'.faceCoordinates j)
      (B.faceBasis i) (B'.faceBasis j) := by
  have hsub : (B.face i).carrier ∩ (B'.face j).carrier ⊆
      (B.endpointEdge right).map '' Icc (0 : ℝ) 1 := by
    rw [← hinter]
    exact fun z hz => ⟨mem_iUnion.mpr ⟨i, hz.1⟩, mem_iUnion.mpr ⟨j, hz.2⟩⟩
  apply band_faces_compatible_of_intersection B B' i j
  by_cases hi : i = if right then (B.lastCell, false) else (B.firstCell, true)
  · by_cases hj : j = if right' then (B'.lastCell, false) else (B'.firstCell, true)
    · subst i
      subst j
      have hedge :
          ((B.face (if right then (B.lastCell, false) else (B.firstCell, true))).boundary
            (if right then 0 else 2)).map '' Icc (0 : ℝ) 1 =
              (B.endpointEdge right).map '' Icc (0 : ℝ) 1 := by cases right <;> rfl
      have hedge' :
          ((B'.face (if right' then (B'.lastCell, false) else (B'.firstCell, true))).boundary
            (if right' then 0 else 2)).map '' Icc (0 : ℝ) 1 =
              (B'.endpointEdge right').map '' Icc (0 : ℝ) 1 := by cases right' <;> rfl
      refine Or.inl ⟨if right then 0 else 2, if right' then 0 else 2, ?_,
        hedge.trans (hshared.trans hedge'.symm)⟩
      rw [hedge]
      apply Subset.antisymm hsub
      exact fun z hz => ⟨m64Intrinsic_band_endpoint_subset_selected_face B right hz,
        m64Intrinsic_band_endpoint_subset_selected_face B' right' (hshared ▸ hz)⟩
    · refine Or.inr ⟨(B'.endpointEdge right').map (if right' then 1 else 0), ?_⟩
      intro z hz
      exact m64Intrinsic_band_endpoint_inter_other_face B' right' j hj
        ⟨hshared ▸ hsub hz, hz.2⟩
  · refine Or.inr ⟨(B.endpointEdge right).map (if right then 1 else 0), ?_⟩
    intro z hz
    exact m64Intrinsic_band_endpoint_inter_other_face B right i hi ⟨hsub hz, hz.1⟩

end PoincareConjecture
