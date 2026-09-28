import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalExteriorMarks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalExteriorGapCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalSectorAttachmentFibers

set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_heightGraph_of_projection_homeomorph
    {gap : Set (E × F)} {arc : Set E} (e : gap ≃ₜ arc) (he : e.symm.IsFinitePL)
    (hproj : ∀ x : gap, (e x : E) = (x : E × F).1) :
    ∃ f : E → F, FinitePiecewiseAffineOn f arc ∧
      heightGraph f '' arc = gap ∧
      ∀ x : arc, heightGraph f x = (e.symm x : E × F) := by
  obtain ⟨v, hv, hval⟩ := he
  let f : E → F := Prod.snd ∘ v
  have hf := hv.postcomp (ContinuousLinearMap.snd ℝ E F).toContinuousAffineMap
  have hgraph (x : arc) : heightGraph f x = (e.symm x : E × F) := by
    apply Prod.ext
    · exact ((hproj (e.symm x)).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply x))).symm
    · change (v x).2 = (e.symm x : E × F).2
      exact congrArg Prod.snd (hval x).symm
  refine ⟨f, hf, ?_, hgraph⟩
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [hgraph ⟨x, hx⟩]
    exact (e.symm ⟨x, hx⟩).property
  · intro y hy
    refine ⟨e ⟨y, hy⟩, (e ⟨y, hy⟩).property, ?_⟩
    exact (hgraph (e ⟨y, hy⟩)).trans
      (congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩))

theorem exists_primal_sector_graph_attachment
    {s b : Set (E × F)} (hs : IsFinitePLBallPair (ℝ × ℝ) s b)
    {d q : Set E} {marks : Fin 4 → E}
    (C : OriginalPrimalSectorDecomposition d q marks) (hm : Function.Injective marks)
    (gap : Fin 4 → Set (E × F)) (hgap : ∀ i, gap i ⊆ b)
    (hdis : Pairwise (fun i j ↦ Disjoint (gap i) (gap j)))
    (σ : Fin 4 ≃ Fin 4)
    (e : ∀ i, gap i ≃ₜ C.rim (σ i))
    (he : ∀ i, (e i).symm.IsFinitePL)
    (hproj : ∀ i (x : gap i), (e i x : E) = (x : E × F).1) :
    ∃ (g : Fin 4 → E → F) (k : Fin 4 → (E × F) → ℝ),
      (∀ i, FinitePiecewiseAffineOn (g i) (C.sector i)) ∧
      (∀ i, heightGraph (g i) '' C.rim i = gap (σ.symm i)) ∧
      (∀ i, FinitePiecewiseAffineOn (k i) (heightGraph (g i) '' C.sector i)) ∧
      (∀ i x, x ∈ C.sector i → k i (heightGraph (g i) x) ∈ Icc 0 1 ∧
        (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (graphAttachmentCarrier g k s C.sector)
        (graphAttachmentRim g k b (fun i ↦ C.rim i ∪ (C.spoke i ∪ C.spoke (i + 1)))
          C.rim (fun i ↦ marks (C.order i)) (fun i ↦ marks (C.order (i + 1)))) ∧
      FinitePiecewiseAffineOn (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1)
        (graphAttachmentCarrier g k s C.sector) ∧
      (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ''
        graphAttachmentCarrier g k s C.sector = Prod.fst '' s ∪ d := by
  choose f hf hfi hfv using fun i ↦
    exists_heightGraph_of_projection_homeomorph (e i) (he i) (hproj i)
  let f' : Fin 4 → E → F := fun i ↦ f (σ.symm i)
  have hf' (i : Fin 4) : FinitePiecewiseAffineOn (f' i) (C.rim i) := by
    simpa only [Equiv.apply_symm_apply] using hf (σ.symm i)
  have hfi' (i : Fin 4) : heightGraph (f' i) '' C.rim i = gap (σ.symm i) := by
    simpa only [Equiv.apply_symm_apply] using hfi (σ.symm i)
  have hbound (i : Fin 4) : heightGraph (f' i) '' C.rim i ⊆ b := by
    rw [hfi']; exact hgap _
  have hdis' : Pairwise (fun i j ↦ Disjoint (heightGraph (f' i) '' C.rim i)
      (heightGraph (f' j) '' C.rim j)) := by
    intro i j hij
    rw [hfi', hfi']
    exact hdis (fun h ↦ hij (σ.symm.injective h))
  have hend (i : Fin 4) : marks (C.order i) ≠ marks (C.order (i + 1)) := by
    intro h
    have hi := C.order.injective (hm h)
    fin_cases i <;> contradiction
  obtain ⟨g, k, hg, hk, hz, hdisk, hmap, himage, _⟩ :=
    exists_boundary_graph_attachments hs C.sector_ball C.rim_ball
      (fun _ ↦ subset_union_left) hend f' hf' hbound hdis'
  refine ⟨g, k, fun i ↦ (hg i).1, ?_, hk, hz, hdisk, hmap, ?_⟩
  · intro i
    have hgg : heightGraph (g i) '' C.rim i = heightGraph (f' i) '' C.rim i :=
      Set.image_congr (fun x hx ↦ Prod.ext rfl ((hg i).2 hx))
    exact hgg.trans (hfi' i)
  · rw [himage]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact C.sector_subset i hxi
    · intro hx
      rcases C.sector_cover.symm.subset hx with (hx | hx) | (hx | hx)
      · exact mem_iUnion.mpr ⟨0, hx⟩
      · exact mem_iUnion.mpr ⟨1, hx⟩
      · exact mem_iUnion.mpr ⟨2, hx⟩
      · exact mem_iUnion.mpr ⟨3, hx⟩

section OriginalSurface

variable [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  (P : SimpleGraph K.vertices)
  (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
  (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
  (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
  [Fintype (ResidualComplementaryEdge K P D)]
  (labels : ResidualComplementaryEdge K P D ≃ Fin 2)

structure OriginalPrimalCutDiskData where
  bands : ∀ s : ResidualComplementaryEdge K P D,
    OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val)
  exteriorHeight : ResidualHalfBandIndex K P D → E → ℝ
  exteriorHeightPL : ∀ i, FinitePiecewiseAffineOn (exteriorHeight i) ((bands i.1).piece i.2)
  exteriorHeight_spec : ∀ i x, x ∈ (bands i.1).piece i.2 → exteriorHeight i x ∈ Icc 0 1 ∧
    (exteriorHeight i x = 0 ↔ x ∈ (bands i.1).attachment i.2)
  exteriorDisk : IsFinitePLBallPair (ℝ × ℝ)
    (complementaryCutCarrier K P D hD hcofaces bands exteriorHeight)
    (complementaryCutRim K P D hD hcofaces bands exteriorHeight)
  gaps : ExteriorGapCoordinates K P D hD hcofaces bands exteriorHeight labels
  sectors : OriginalPrimalSectorDecomposition
    (K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
    (K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP))
    (originalExteriorMarks K P D hcofaces bands labels)
  matching : Fin 4 ≃ Fin 4
  sectorHeight : Fin 4 → E → (ResidualHalfBandIndex K P D → ℝ)
  freshHeight : Fin 4 → (E × (ResidualHalfBandIndex K P D → ℝ)) → ℝ
  sectorHeightPL : ∀ i, FinitePiecewiseAffineOn (sectorHeight i) (sectors.sector i)
  sectorGraph_eq_gap : ∀ i,
    heightGraph (sectorHeight i) '' sectors.rim i = gaps.gap (matching.symm i)
  freshHeightPL : ∀ i, FinitePiecewiseAffineOn (freshHeight i)
    (heightGraph (sectorHeight i) '' sectors.sector i)
  freshHeight_spec : ∀ i x, x ∈ sectors.sector i →
    freshHeight i (heightGraph (sectorHeight i) x) ∈ Icc 0 1 ∧
      (freshHeight i (heightGraph (sectorHeight i) x) = 0 ↔ x ∈ sectors.rim i)
  disk : IsFinitePLBallPair (ℝ × ℝ)
    (graphAttachmentCarrier sectorHeight freshHeight
      (complementaryCutCarrier K P D hD hcofaces bands exteriorHeight) sectors.sector)
    (graphAttachmentRim sectorHeight freshHeight
      (complementaryCutRim K P D hD hcofaces bands exteriorHeight)
      (fun i ↦ sectors.rim i ∪ (sectors.spoke i ∪ sectors.spoke (i + 1)))
      sectors.rim (fun i ↦ originalExteriorMarks K P D hcofaces bands labels (sectors.order i))
      (fun i ↦ originalExteriorMarks K P D hcofaces bands labels (sectors.order (i + 1))))
  sourceMapPL : FinitePiecewiseAffineOn
    (fun p : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ) ↦ p.1.1)
    (graphAttachmentCarrier sectorHeight freshHeight
      (complementaryCutCarrier K P D hD hcofaces bands exteriorHeight) sectors.sector)
  sourceMap_image :
    (fun p : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ) ↦ p.1.1) ''
      graphAttachmentCarrier sectorHeight freshHeight
        (complementaryCutCarrier K P D hD hcofaces bands exteriorHeight) sectors.sector = K.space

noncomputable def OriginalPrimalCutDiskData.carrier
    (C : OriginalPrimalCutDiskData K P D hD hcofaces hP labels) :
    Set ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)) :=
  graphAttachmentCarrier C.sectorHeight C.freshHeight
    (complementaryCutCarrier K P D hD hcofaces C.bands C.exteriorHeight) C.sectors.sector

noncomputable def OriginalPrimalCutDiskData.rim
    (C : OriginalPrimalCutDiskData K P D hD hcofaces hP labels) :
    Set ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)) :=
  graphAttachmentRim C.sectorHeight C.freshHeight
    (complementaryCutRim K P D hD hcofaces C.bands C.exteriorHeight)
    (fun i ↦ C.sectors.rim i ∪ (C.sectors.spoke i ∪ C.sectors.spoke (i + 1)))
    C.sectors.rim
    (fun i ↦ originalExteriorMarks K P D hcofaces C.bands labels (C.sectors.order i))
    (fun i ↦ originalExteriorMarks K P D hcofaces C.bands labels (C.sectors.order (i + 1)))

def OriginalPrimalCutDiskData.sourceMap
    (_C : OriginalPrimalCutDiskData K P D hD hcofaces hP labels) :
    ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)) → E := fun p ↦ p.1.1

theorem nonempty_originalPrimalCutDiskData
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hPtree : P.IsTree) (hDtree : D.IsTree) :
    Nonempty (OriginalPrimalCutDiskData K P D hD hcofaces hP labels) := by
  obtain ⟨B, h, hh, hz, hdisk, _, ⟨C⟩⟩ :=
    exists_original_exterior_gaps K P D hD hcofaces labels hpure hlinks hDtree
  obtain ⟨T⟩ := nonempty_originalExteriorPrimalSectors K P D hcofaces B labels
    hpure hlinks hP hPtree
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  obtain ⟨σ, hσ⟩ := exteriorGap_projection_matching K P D hD hcofaces B h labels C
    hP hbound (fun i x hx ↦ (hz i x hx).2) _
    (originalExteriorMarks_injective K P D hcofaces B labels)
    (originalExteriorMarks_range K P D hcofaces B labels) T
  choose e he hei heval using hσ
  obtain ⟨g, k, hg, hgap, hk, hkz, hwhole, hmap, himage⟩ :=
    exists_primal_sector_graph_attachment hdisk T
      (originalExteriorMarks_injective K P D hcofaces B labels)
      C.gap C.gap_subset C.gaps_pairwise_disjoint σ e hei heval
  refine ⟨{
    bands := B, exteriorHeight := h, exteriorHeightPL := hh, exteriorHeight_spec := hz
    exteriorDisk := hdisk, gaps := C, sectors := T, matching := σ
    sectorHeight := g, freshHeight := k, sectorHeightPL := hg, sectorGraph_eq_gap := hgap
    freshHeightPL := hk, freshHeight_spec := hkz, disk := hwhole
    sourceMapPL := hmap, sourceMap_image := ?_ }⟩
  rw [himage, complementaryCut_projection_image K P D hD hcofaces hP hbound B h]
  rw [union_comm, ← K.barycentricSubdivision.vertexDualUnion_union]
  simp only [union_compl_self, K.barycentricSubdivision.vertexDualUnion_univ]
  exact K.barycentricSubdivision_isSubdivision.space_eq

end OriginalSurface
end PoincareConjecture.M76.OriginalTriangleCopies
