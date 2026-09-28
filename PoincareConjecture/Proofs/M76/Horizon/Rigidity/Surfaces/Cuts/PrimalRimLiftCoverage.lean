import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalExteriorMarks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ComplementaryRimProjection









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  (P : SimpleGraph K.vertices)
  (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
  (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
  [Fintype (ResidualComplementaryEdge K P D)]
  (B : ∀ s : ResidualComplementaryEdge K P D,
    OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
  (h : ResidualHalfBandIndex K P D → E → ℝ)
  (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
  (hbound : ∀ t ∈ K.faces, t.card ≤ 3)

private theorem residualBand_primal_contacts
    (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBand K (complementaryOriginalEdge K P hcofaces s.val))
    (hxP : x ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    x ∈ primalEdgeContact K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends 0) ∪
      primalEdgeContact K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends 1) := by
  have he := (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
    (originalTriangleCofaceCounts K hcofaces) s.val).property
  have hc := (edgeCentroidBlock_inter_primal K P hP _ he).subset ⟨hx,hxP⟩
  obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp hc
  change v ∈ (complementaryOriginalEdge K P hcofaces s.val).val at hv
  rw [(B s).edge_eq] at hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact Or.inl hxv
  · exact Or.inr ((Finset.mem_singleton.mp hv) ▸ hxv)

include hbound

theorem complementary_attachment_primal_contact
    (i : ResidualHalfBandIndex K P D) {x : E}
    (hx : x ∈ (B i.1).attachment i.2)
    (hxP : x ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    x ∈ ({(B i.1).firstCorner i.2,(B i.1).secondCorner i.2} : Set E) := by
  have hxband := (B i.1).piece_subset_band i.2 ((B i.1).attachment_subset_piece i.2 hx)
  have hcontacts := residualBand_primal_contacts K P D hcofaces B hP i.1 hxband hxP
  have hcorner (j : Fin 2)
      (hj : x ∈ primalEdgeContact K (complementaryOriginalEdge K P hcofaces i.1.val)
        ((B i.1).ends j)) :
      x = residualBandCorner K (complementaryOriginalEdge K P hcofaces i.1.val)
        ((B i.1).ends j) ((B i.1).coface i.2).val := by
    apply (primal_coface_contact_inter K hbound _ ((B i.1).ends j) ?_
      ((B i.1).coface i.2).property.1 ((B i.1).coface i.2).property.2
      ((B i.1).edge_subset i.2)).subset
    · exact ⟨hj,hx⟩
    · fin_cases j <;> simp [(B i.1).edge_eq]
  rcases hcontacts with ha | hb
  · exact Or.inl (hcorner 0 ha)
  · exact Or.inr (hcorner 1 hb)

private theorem selectedDual_inter_primal_subset_rim {x : E}
    (hxD : x ∈ K.barycentricSubdivision.vertexDualUnion
      (selectedDualCentroidSet K P D hD hcofaces))
    (hxP : x ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    x ∈ K.barycentricSubdivision.vertexDualRim (selectedDualCentroidSet K P D hD hcofaces) := by
  refine ⟨hxD,?_⟩
  obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hxP
  refine mem_iUnion₂.mpr ⟨p,?_,hxp⟩
  intro hpD
  have hcomp := (complementaryCentroid_range_eq_selected_union_residual K P D hD hcofaces).symm.subset
    (Or.inl hpD)
  rw [complementaryCentroid_range_eq_compl_primal K P hP hbound hcofaces] at hcomp
  exact hcomp hp



theorem complementaryCut_over_primalRim_subset_rim
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) :
    complementaryCutCarrier K P D hD hcofaces B h ∩
        Prod.fst ⁻¹' K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) ⊆
      complementaryCutRim K P D hD hcofaces B h := by
  rintro z ⟨hzC,hzP⟩
  change z ∈ separatedCarrier h _ _ Finset.univ at hzC
  rcases hzC with ⟨x,hx,rfl⟩ | hzC
  · have hxP := hzP.1
    have hxr := selectedDual_inter_primal_subset_rim K P D hD hcofaces hP hbound hx hxP
    apply (zeroSheet_mem_separatedRim_iff h Finset.univ hxr).mpr
    intro i _ hxi
    exact complementary_attachment_primal_contact K P D hcofaces B hP hbound i hxi hxP
  · obtain ⟨i,_,x,hx,rfl⟩ := mem_iUnion₂.mp hzC
    have hxP := hzP.1
    have hxband := (B i.1).piece_subset_band i.2 hx
    have hcontacts := residualBand_primal_contacts K P D hcofaces B hP i.1 hxband hxP
    have hxbandrim : x ∈ residualBandRim K (complementaryOriginalEdge K P hcofaces i.1.val) := by
      rcases hcontacts with ha | hb
      · exact primalEdgeContact_subset_bandRim K _ _ (by simp [(B i.1).edge_eq]) ha
      · exact primalEdgeContact_subset_bandRim K _ _ (by simp [(B i.1).edge_eq]) hb
    have hxrim : x ∈ (B i.1).rim i.2 := Or.inl ((B i.1).piece_outer i.2 |>.subset ⟨hx,hxbandrim⟩)
    apply (separatedSheet_mem_separatedRim_iff h (fun j => ((B j.1).disk j.2).1) hz
      (complementaryHalfBand_attachments_pairwise K P D hcofaces B) Finset.univ
      (Finset.mem_univ i) hxrim).mpr
    intro hxi
    exact complementary_attachment_primal_contact K P D hcofaces B hP hbound i hxi hxP

variable (labels : ResidualComplementaryEdge K P D ≃ Fin 2)
  (C : ExteriorGapCoordinates K P D hD hcofaces B h labels)

theorem exteriorGap_projection_subset_primalRim
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) (i : Fin 4) :
    Prod.fst '' C.gap i ⊆
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
  rintro x ⟨z,hzg,rfl⟩
  by_cases he : z ∈ ({C.bridgeFinish i,C.bridgeStart (i+1)} : Set _)
  · have hm := exteriorGapEndpoints_project_quarterMarks K P D hD hcofaces B h labels C i he
    rw [← originalExteriorMarks_range K P D hcofaces B labels] at hm
    obtain ⟨j,hj⟩ := hm
    exact hj ▸ originalExteriorMarks_mem_primalRim K P D hcofaces B labels hP j
  · have hzint : z ∈ exteriorGapInterior K P D hD hcofaces B h labels C i := ⟨hzg,he⟩
    apply complementaryCut_rim_without_bridges_projects_to_primalRim K P D hD hcofaces B h
      hP hbound hz
    exact ⟨z,⟨C.gap_subset i hzg,fun hc => Set.disjoint_left.mp
      (exteriorGapInterior_disjoint_copies K P D hD hcofaces B h labels C i) hzint hc⟩,rfl⟩

private theorem copiedBridge_over_primalRim_is_endpoint
    (k : Fin 4) {z : E × (ResidualHalfBandIndex K P D → ℝ)}
    (hzB : z ∈ exteriorCopiedBridge K P D hcofaces B h (exteriorFourIndex K P D labels k))
    (hzP : z.1 ∈ K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) :
    z ∈ ({exteriorCopiedMark K P D hcofaces B h (exteriorFourIndex K P D labels k) 0,
      exteriorCopiedMark K P D hcofaces B h (exteriorFourIndex K P D labels k) 1} : Set _) := by
  obtain ⟨x,hx,rfl⟩ := hzB
  have hm := (residualBridge_inter_primalRim K P D hcofaces B hP
    (exteriorFourIndex K P D labels k).1).subset ⟨hx,hzP⟩
  rcases hm with he | he
  · exact Or.inl (congrArg (separatedSheet h (exteriorFourIndex K P D labels k)) he)
  · exact Or.inr (congrArg (separatedSheet h (exteriorFourIndex K P D labels k)) he)



theorem complementaryCut_over_primalRim_eq_gaps
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) :
    complementaryCutCarrier K P D hD hcofaces B h ∩
        Prod.fst ⁻¹' K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) =
      ⋃ i : Fin 4, C.gap i := by
  apply Subset.antisymm
  · intro z hzlift
    have hzr := complementaryCut_over_primalRim_subset_rim K P D hD hcofaces B h
      hP hbound hz hzlift
    rcases C.gaps_cover.symm.subset hzr with ⟨k,hzk⟩ | ⟨i,hzi⟩
    · have hends := copiedBridge_over_primalRim_is_endpoint K P D hcofaces B h
        hP hbound labels k hzk hzlift.2
      have hp := C.bridge_endpoints (C.bridgeOrder.symm k)
      rw [C.bridgeOrder.apply_symm_apply k] at hp
      have hends' := hp.symm.subset hends
      rcases hends' with he | he
      · let j := C.bridgeOrder.symm k
        have hg := C.gap_isFinitePLBallPair_cyclic (j-1)
        rw [sub_add_cancel] at hg
        exact mem_iUnion.mpr ⟨j-1,hg.1 (Or.inr he)⟩
      · exact mem_iUnion.mpr ⟨C.bridgeOrder.symm k,
          (C.gap_isFinitePLBallPair_cyclic _).1 (Or.inl he)⟩
    · exact mem_iUnion.mpr ⟨i,hzi⟩
  · intro z hzunion
    obtain ⟨i,hzi⟩ := mem_iUnion.mp hzunion
    exact ⟨complementaryCut_rim_subset_carrier K P D hD hcofaces B h (C.gap_subset i hzi),
      exteriorGap_projection_subset_primalRim K P D hD hcofaces B h hP hbound labels C hz i
        ⟨z,hzi,rfl⟩⟩

end PoincareConjecture.M76.OriginalTriangleCopies
