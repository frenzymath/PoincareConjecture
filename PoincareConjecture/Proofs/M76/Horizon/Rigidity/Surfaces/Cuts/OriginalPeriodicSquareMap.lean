import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalPeriodicCutRectangle
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PeriodNormalization









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains
open PoincareConjecture.M76.PeriodicSquare

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)
  (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

local notation "sm" => A.sourceMap K P D hD hcofaces hP labels

private def unitSquareCorner (i : Fin 4) : Square 1 :=
  ![(⟨1,by norm_num⟩,⟨0,by norm_num⟩),
    (⟨1,by norm_num⟩,⟨1,by norm_num⟩),
    (⟨0,by norm_num⟩,⟨1,by norm_num⟩),
    (⟨0,by norm_num⟩,⟨0,by norm_num⟩)] i

private theorem unitSquareCorner_projection (i : Fin 4) : projection 1 (unitSquareCorner i) = 0 := by
  apply (projection_eq_zero_iff 1 _).mpr
  fin_cases i <;> simp [unitSquareCorner]

include hbound



theorem nonempty_sourceSquareMap_of_source_reversal
    (hrev : ∀ i : Fin 4, sm (A.bridgeBegin (A.arcPairing i)) =
      sm (A.bridgeEnd i)) : Nonempty (SourceSquareMap 1 K) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨C,H,G,e,d,hC,hH,hG,hbottom,htop,hleft,hright⟩ :=
    A.exists_matched_original_rectangle hbound hrev
  let Q : Square 1 ≃ₜ A.carrier := (squareCarrierEquiv 1).trans C
  have hQB (t : Icc (0 : ℝ) 1) : (Q (sidePoint 1 0 false t)).val = e t := hbottom t
  have hQT (t : Icc (0 : ℝ) 1) : (Q (sidePoint 1 0 true t)).val = H (e t) := htop t
  have hQL (t : Icc (0 : ℝ) 1) : (Q (sidePoint 1 1 false t)).val = d t := hleft t
  have hQR (t : Icc (0 : ℝ) 1) : (Q (sidePoint 1 1 true t)).val = G (d t) := hright t
  have hQcorner (i : Fin 4) : (Q (unitSquareCorner i)).val = A.gapCenter i := by
    fin_cases i
    · change (Q ((⟨1,by norm_num⟩,⟨0,by norm_num⟩) : Square 1)).val = A.gapCenter 0
      apply (A.longBoundaryArc_inter_next hbound 0).subset
      constructor
      · rw [show ((⟨1,by norm_num⟩,⟨0,by norm_num⟩) : Square 1) = sidePoint 1 0 false ⟨1,by norm_num⟩ from rfl,hQB]
        exact (e _).property
      · rw [show ((⟨1,by norm_num⟩,⟨0,by norm_num⟩) : Square 1) = sidePoint 1 1 true ⟨0,by norm_num⟩ from rfl,hQR]
        exact (G (d _)).property
    · change (Q ((⟨1,by norm_num⟩,⟨1,by norm_num⟩) : Square 1)).val = A.gapCenter 1
      apply (A.longBoundaryArc_inter_next hbound 1).subset
      constructor
      · rw [show ((⟨1,by norm_num⟩,⟨1,by norm_num⟩) : Square 1) = sidePoint 1 1 true ⟨1,by norm_num⟩ from rfl,hQR]
        exact (G (d _)).property
      · rw [show ((⟨1,by norm_num⟩,⟨1,by norm_num⟩) : Square 1) = sidePoint 1 0 true ⟨1,by norm_num⟩ from rfl,hQT]
        exact (H (e _)).property
    · change (Q ((⟨0,by norm_num⟩,⟨1,by norm_num⟩) : Square 1)).val = A.gapCenter 2
      apply (A.longBoundaryArc_inter_next hbound 2).subset
      constructor
      · rw [show ((⟨0,by norm_num⟩,⟨1,by norm_num⟩) : Square 1) = sidePoint 1 0 true ⟨0,by norm_num⟩ from rfl,hQT]
        exact (H (e _)).property
      · rw [show ((⟨0,by norm_num⟩,⟨1,by norm_num⟩) : Square 1) = sidePoint 1 1 false ⟨1,by norm_num⟩ from rfl,hQL]
        exact (d _).property
    · change (Q ((⟨0,by norm_num⟩,⟨0,by norm_num⟩) : Square 1)).val = A.gapCenter 3
      apply (A.longBoundaryArc_inter_next hbound 3).subset
      constructor
      · rw [show ((⟨0,by norm_num⟩,⟨0,by norm_num⟩) : Square 1) = sidePoint 1 1 false ⟨0,by norm_num⟩ from rfl,hQL]
        exact (d _).property
      · rw [show ((⟨0,by norm_num⟩,⟨0,by norm_num⟩) : Square 1) = sidePoint 1 0 false ⟨0,by norm_num⟩ from rfl,hQB]
        exact (e _).property
  have hcenter (z : Square 1) (hz : sm (Q z) = A.sectors.center) :
      projection 1 z = 0 := by
    have hf : (Q z).val ∈ A.carrier ∩ sm ⁻¹' {A.sectors.center} := ⟨(Q z).property,hz⟩
    rw [A.sourceMap_center_fiber hbound] at hf
    obtain ⟨i,hi⟩ := hf
    have he : (Q z).val = (Q (unitSquareCorner (A.matching.symm i))).val := by
      rw [hQcorner]
      change (Q z).val = A.sectorCopy (A.matching (A.matching.symm i)) A.sectors.center
      rw [A.matching.apply_symm_apply]
      exact hi.symm
    have hz' := Q.injective (Subtype.ext he)
    rw [hz',unitSquareCorner_projection]
  have hop := A.arcPairing_opposite_of_source_reversal hrev
  have hfH (p : A.longBoundaryArc 0) (hp : sm p ≠ A.sectors.center) :
      A.carrier ∩ sm ⁻¹' {sm p} = {p.val,(H p).val} := by
    have h := A.whole_fiber_of_longBoundaryArc_pairing hbound 0
    rw [show A.arcPairing 0 = 2 from hop 0] at h
    exact h H hH p hp
  have hfG (p : A.longBoundaryArc 3) (hp : sm p ≠ A.sectors.center) :
      A.carrier ∩ sm ⁻¹' {sm p} = {p.val,(G p).val} := by
    have h := A.whole_fiber_of_longBoundaryArc_pairing hbound 3
    rw [show A.arcPairing 3 = 1 from hop 3] at h
    exact h G hG p hp
  have hfromH (t : Icc (0 : ℝ) 1) (hp : sm (e t) ≠ A.sectors.center)
      (z : Square 1) (hz : sm (Q z) = sm (e t)) :
      projection 1 z = projection 1 (sidePoint 1 0 false t) := by
    have hf : (Q z).val ∈ A.carrier ∩ sm ⁻¹' {sm (e t)} := ⟨(Q z).property,hz⟩
    rw [hfH (e t) hp] at hf
    rcases hf with hf | hf
    · have he : z = sidePoint 1 0 false t := Q.injective (Subtype.ext (hf.trans (hQB t).symm))
      rw [he]
    · have he : z = sidePoint 1 0 true t := Q.injective (Subtype.ext (hf.trans (hQT t).symm))
      rw [he]
      exact sidePoint_projection_eq_opposite 1 0 true t
  have hfromG (t : Icc (0 : ℝ) 1) (hp : sm (d t) ≠ A.sectors.center)
      (z : Square 1) (hz : sm (Q z) = sm (d t)) :
      projection 1 z = projection 1 (sidePoint 1 1 false t) := by
    have hf : (Q z).val ∈ A.carrier ∩ sm ⁻¹' {sm (d t)} := ⟨(Q z).property,hz⟩
    rw [hfG (d t) hp] at hf
    rcases hf with hf | hf
    · have he : z = sidePoint 1 1 false t := Q.injective (Subtype.ext (hf.trans (hQL t).symm))
      rw [he]
    · have he : z = sidePoint 1 1 true t := Q.injective (Subtype.ext (hf.trans (hQR t).symm))
      rw [he]
      exact sidePoint_projection_eq_opposite 1 1 true t
  have hnoextra (z w : Square 1) (hzw : sm (Q z) = sm (Q w)) :
      projection 1 z = projection 1 w := by
    by_cases hc : sm (Q z) = A.sectors.center
    · exact (hcenter z hc).trans (hcenter w (hzw.symm.trans hc)).symm
    rcases A.sourceMap_fiber_eq_or_rim hbound (Q z).property (Q w).property hzw with he | hrim
    · exact congrArg (projection 1) (Q.injective (Subtype.ext he))
    have hi : ∃ i : Fin 4, (Q z).val ∈ A.longBoundaryArc i := by
      exact mem_iUnion.mp (A.longBoundaryArcs_cover.symm.subset hrim.1)
    obtain ⟨i,hi⟩ := hi
    fin_cases i
    · let p : A.longBoundaryArc 0 := ⟨(Q z).val,hi⟩
      let t := e.symm p
      have hpe : (e t).val = (Q z).val := congrArg Subtype.val (e.apply_symm_apply p)
      have hp : sm (e t) ≠ A.sectors.center := by rw [hpe]; exact hc
      exact (hfromH t hp z (congrArg sm hpe.symm)).trans
        (hfromH t hp w (hzw.symm.trans (congrArg sm hpe.symm))).symm
    · let p : A.longBoundaryArc 1 := ⟨(Q z).val,hi⟩
      let t := d.symm (G.symm p)
      have hpe : (G (d t)).val = (Q z).val := by
        rw [show d t = G.symm p from d.apply_symm_apply (G.symm p),G.apply_symm_apply]
      have hsource : sm (Q z) = sm (d t) :=
        (congrArg sm hpe).symm.trans (hG (d t))
      have hp : sm (d t) ≠ A.sectors.center := by rw [← hsource]; exact hc
      exact (hfromG t hp z hsource).trans (hfromG t hp w (hzw.symm.trans hsource)).symm
    · let p : A.longBoundaryArc 2 := ⟨(Q z).val,hi⟩
      let t := e.symm (H.symm p)
      have hpe : (H (e t)).val = (Q z).val := by
        rw [show e t = H.symm p from e.apply_symm_apply (H.symm p),H.apply_symm_apply]
      have hsource : sm (Q z) = sm (e t) :=
        (congrArg sm hpe).symm.trans (hH (e t))
      have hp : sm (e t) ≠ A.sectors.center := by rw [← hsource]; exact hc
      exact (hfromH t hp z hsource).trans (hfromH t hp w (hzw.symm.trans hsource)).symm
    · let p : A.longBoundaryArc 3 := ⟨(Q z).val,hi⟩
      let t := d.symm p
      have hpe : (d t).val = (Q z).val := congrArg Subtype.val (d.apply_symm_apply p)
      have hp : sm (d t) ≠ A.sectors.center := by rw [hpe]; exact hc
      exact (hfromG t hp z (congrArg sm hpe.symm)).trans
        (hfromG t hp w (hzw.symm.trans (congrArg sm hpe.symm))).symm
  let f : C(Square 1,K.space) :=
    ⟨fun z => ⟨sm (Q z),A.sourceMap_image.subset (mem_image_of_mem _ (Q z).property)⟩,
      by change Continuous (fun z => (⟨(Q z).val.1.1,_⟩ : K.space)); fun_prop⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨p,hp,hpx⟩ := A.sourceMap_image.symm.subset hx
    obtain ⟨z,hz⟩ := Q.surjective ⟨p,hp⟩
    refine ⟨z,Subtype.ext ?_⟩
    change sm (Q z) = x
    rw [hz]
    exact hpx
  obtain ⟨c,hc,hcv⟩ := hC
  let F := sm ∘ c
  have hm : MapsTo c (squareCarrier 1) A.carrier := by
    intro x hx
    rw [← hcv ⟨x,hx⟩]
    exact (C ⟨x,hx⟩).property
  have hF : FinitePiecewiseAffineOn F (squareCarrier 1) := A.sourceMapPL.comp hc hm
  have hvalue (z : Square 1) : F (z.1,z.2) = sm (Q z) := by
    change sm (c ((squareCarrierEquiv 1 z).1)) = sm ((C (squareCarrierEquiv 1 z)).val)
    rw [← hcv (squareCarrierEquiv 1 z)]
  refine ⟨SourceSquareMap.of_ambient_closed_filling (p := 1) f F hF hvalue hsurj ?_ ?_⟩
  · intro i t
    rw [hvalue,hvalue]
    fin_cases i
    · change sm (Q (sidePoint 1 0 false t)) = sm (Q (sidePoint 1 0 true t))
      rw [hQB,hQT]
      exact (hH (e t)).symm
    · change sm (Q (sidePoint 1 1 false t)) = sm (Q (sidePoint 1 1 true t))
      rw [hQL,hQR]
      exact (hG (d t)).symm
  · intro z w hzw
    exact hnoextra z w ((hvalue z).symm.trans (hzw.trans (hvalue w)))

noncomputable def sourceSquareMap_of_source_reversal
    (hrev : ∀ i : Fin 4, sm (A.bridgeBegin (A.arcPairing i)) =
      sm (A.bridgeEnd i)) : SourceSquareMap 1 K :=
  Classical.choice (A.nonempty_sourceSquareMap_of_source_reversal hbound hrev)

noncomputable def sourceSquareMap64_of_source_reversal
    (hrev : ∀ i : Fin 4, sm (A.bridgeBegin (A.arcPairing i)) =
      sm (A.bridgeEnd i)) : SourceSquareMap 64 K :=
  (letI : Fact (0 < (64 : ℝ)) := ⟨by norm_num⟩; (A.sourceSquareMap_of_source_reversal hbound hrev).withPeriod 64)

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
