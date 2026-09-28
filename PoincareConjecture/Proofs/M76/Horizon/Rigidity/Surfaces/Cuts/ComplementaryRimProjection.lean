import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ConnectedRimProjection








set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]

omit [Fintype K.vertices] in
theorem OriginalResidualHalfBands.bandRim_four_contacts
    {e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex}
    (B : OriginalResidualHalfBands K e)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) :
    residualBandRim K e =
      (primalEdgeContact K e (B.ends 0) ∪ primalEdgeContact K e (B.ends 1)) ∪
        (B.attachment 0 ∪ B.attachment 1) := by
  have hemap : e.val.map (Function.Embedding.subtype _) =
      {((B.ends 0).val), ((B.ends 1).val)} := by
    simp only [B.edge_eq, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype]
  have hset : {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      e.val.map (Function.Embedding.subtype _) ⊆ s} =
      {(B.coface 0).val, (B.coface 1).val} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · rintro s (rfl | h)
      · exact ⟨(B.coface 0).property.1, (B.coface 0).property.2, B.edge_subset 0⟩
      · exact h ▸ ⟨(B.coface 1).property.1, (B.coface 1).property.2, B.edge_subset 1⟩
    · rw [Set.ncard_pair (fun h ↦ B.coface_ne (Subtype.ext h)),
        hcofaces _ e.property.1 (by rw [Finset.card_map, e.property.2])]
    · exact Set.toFinite _
  rw [hemap] at hset
  simpa only [OriginalResidualHalfBands.attachment, union_assoc] using
    residualBandRim_eq_four_contacts K hbound e B.edge_eq hset

omit [Fintype K.vertices] in
theorem primalEdgeContact_subset_primalUnion
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) (v : K.vertices) :
    primalEdgeContact K e v ⊆
      K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) := by
  intro x hx
  have hpair := (K.barycentricSubdivision.vertex_dualBlocks_space_inter
    (originalVertexCentroid K v).val (originalEdgeCentroid K e).val).symm.subset hx
  exact mem_iUnion₂.mpr ⟨originalVertexCentroid K v,
    originalVertexCentroid_mem_primalCentroidSet K P hP v, hpair.1⟩

omit [Fintype K.vertices] in
theorem OriginalResidualHalfBands.corners_subset_primalUnion
    {e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex}
    (B : OriginalResidualHalfBands K e)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (i : Fin 2) : {B.firstCorner i, B.secondCorner i} ⊆
      K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) := by
  have hcorner (j : Fin 2) : residualBandCorner K e (B.ends j) (B.coface i).val ∈
      K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) := by
    apply primalEdgeContact_subset_primalUnion K P hP e (B.ends j)
    apply ((primal_coface_contact_inter K hbound e (B.ends j) ?_
      (B.coface i).property.1 (B.coface i).property.2 (B.edge_subset i)).symm.subset
        (mem_singleton _)).1
    fin_cases j <;> simp [B.edge_eq]
  rintro x (rfl | hx)
  · exact hcorner 0
  · exact hx ▸ hcorner 1

variable (P : SimpleGraph K.vertices)
  (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
  (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
  [Fintype (ResidualComplementaryEdge K P D)]
  (B : ∀ s : ResidualComplementaryEdge K P D,
    OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
  (h : ResidualHalfBandIndex K P D → E → ℝ)

theorem complementaryCut_rim_projection_cases
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    {z : E × (ResidualHalfBandIndex K P D → ℝ)}
    (hzrim : z ∈ complementaryCutRim K P D hD hcofaces B h) :
    z.1 ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∨
      z ∈ complementaryBridgeCopies K P D hcofaces B h := by
  classical
  have hsurvive := hzrim.2
  have hatt (i : ResidualHalfBandIndex K P D) {x : E}
      (hx : x ∈ (B i.1).attachment i.2)
      (heq : z = zeroSheet (ι := ResidualHalfBandIndex K P D) x) :
      z.1 ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) := by
    have hcorner : x ∈ ({(B i.1).firstCorner i.2, (B i.1).secondCorner i.2} : Set E) := by
      by_contra hn
      apply hsurvive
      refine mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, ?_⟩
      rw [heq]
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      intro hc
      apply hn
      rcases hc with hc | hc
      · exact Or.inl (congrArg Prod.fst hc)
      · exact Or.inr (congrArg Prod.fst hc)
    rw [heq]
    exact (B i.1).corners_subset_primalUnion K hbound P hP i.2 hcorner
  rcases hzrim.1 with hbase | hsheet
  · obtain ⟨x, hx, rfl⟩ := hbase
    left
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx.2
    have hvcover := (treeCotree_centroid_partition K P hP D hD hbound hcofaces).symm.subset
      (mem_univ v)
    rcases hvcover with (hvP | hvD) | hvR
    · exact mem_iUnion₂.mpr ⟨v, hvP, hxv⟩
    · exact (hv hvD).elim
    · have hxR : x ∈ K.barycentricSubdivision.vertexDualUnion
          (residualCentroidSet K P D hcofaces) := mem_iUnion₂.mpr ⟨v, hvR, hxv⟩
      rw [← residualBand_iUnion_eq_residualCentroidUnion K P D hcofaces] at hxR
      obtain ⟨s, hxs⟩ := mem_iUnion.mp hxR
      have hc := (residualBand_inter_selectedDual_two_contacts K P D hD hcofaces
        s.val s.property ((B s).coface 0) ((B s).coface 1) (B s).coface_ne
        ((B s).edge_subset 0) ((B s).edge_subset 1)).subset ⟨hxs, hx.1⟩
      rcases hc with hc | hc
      · exact hatt (s, 0) hc rfl
      · exact hatt (s, 1) hc rfl
  · obtain ⟨i, _, x, hx, rfl⟩ := mem_iUnion₂.mp hsheet
    have hxpiece := (B i.1).disk i.2 |>.1 hx
    rcases hx with hxouter | hxbridge
    · left
      have hxbandrim : x ∈ residualBandRim K (complementaryOriginalEdge K P hcofaces i.1.val) := by
        have hi : i.2 = 0 ∨ i.2 = 1 := by omega
        rcases hi with hi | hi
        · rw [hi] at hxouter
          exact (B i.1).outer_union.subset (Or.inl hxouter)
        · rw [hi] at hxouter
          exact (B i.1).outer_union.subset (Or.inr hxouter)
      rw [(B i.1).bandRim_four_contacts K hbound hcofaces] at hxbandrim
      rcases hxbandrim with (hxa | hxb) | hxatt
      · exact primalEdgeContact_subset_primalUnion K P hP _ _ hxa
      · exact primalEdgeContact_subset_primalUnion K P hP _ _ hxb
      · have hxD : x ∈ K.barycentricSubdivision.vertexDualUnion
            (selectedDualCentroidSet K P D hD hcofaces) := by
          rcases hxatt with hxatt | hxatt
          · exact ((B i.1).attachment_subset_selectedDualRim K P D hD hcofaces
              i.1.val i.1.property 0 hxatt).1
          · exact ((B i.1).attachment_subset_selectedDualRim K P D hD hcofaces
              i.1.val i.1.property 1 hxatt).1
        have hxown := (OriginalResidualHalfBands.piece_inter_selectedDual K P D hD hbound
          hcofaces i.1.val i.1.property (B i.1) i.2).subset ⟨hxpiece, hxD⟩
        exact hatt i hxown ((separatedSheet_eq_zeroSheet_iff h i x x).mpr
          ⟨rfl, (hz i x hxpiece).mpr hxown⟩)
    · right
      exact mem_iUnion₂.mpr ⟨i.1, i.2, x, hxbridge, rfl⟩

theorem complementaryCut_projection_injOn_without_bridges
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) :
    InjOn Prod.fst (complementaryCutCarrier K P D hD hcofaces B h \
      complementaryBridgeCopies K P D hcofaces B h) := by
  intro p hp q hq hpq
  rcases (complementaryCut_projection_eq_iff K P D hD hcofaces hbound B h hz
    hp.1 hq.1).mp hpq with heq | ⟨s, x, hx, hc⟩
  · exact heq
  · exfalso
    apply hp.2
    rcases hc with hc | hc
    · exact mem_iUnion₂.mpr ⟨s, 0, x, hx, hc.1.symm⟩
    · exact mem_iUnion₂.mpr ⟨s, 1, x, hx, hc.1.symm⟩

theorem complementaryCut_rim_subset_carrier :
    complementaryCutRim K P D hD hcofaces B h ⊆
      complementaryCutCarrier K P D hD hcofaces B h := by
  rintro z ⟨hz, _⟩
  rcases hz with hz | hz
  · obtain ⟨x, hx, rfl⟩ := hz
    exact Or.inl ⟨x, hx.1, rfl⟩
  · obtain ⟨i, hi, x, hx, rfl⟩ := mem_iUnion₂.mp hz
    exact Or.inr (mem_iUnion₂.mpr ⟨i, hi, x, (B i.1).disk i.2 |>.1 hx, rfl⟩)



theorem complementaryCut_rim_without_bridges_projects_to_primalRim
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) :
    Prod.fst '' (complementaryCutRim K P D hD hcofaces B h \
      complementaryBridgeCopies K P D hcofaces B h) ⊆
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
  rintro x ⟨z, ⟨hzrim, hznot⟩, rfl⟩
  have hxP := (complementaryCut_rim_projection_cases K P D hD hcofaces B h
    hP hbound hz hzrim).resolve_right hznot
  have hxC := (complementaryCut_projection_image K P D hD hcofaces hP hbound B h).subset
    ⟨z, complementaryCut_rim_subset_carrier K P D hD hcofaces B h hzrim, rfl⟩
  exact ⟨hxP, hxC⟩

theorem complementary_connected_rim_gap_unique_original_rim
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    (marks : Fin 4 → E)
    (hmarks : range marks = residualQuarterMarks K P D hcofaces B)
    (C : OriginalPrimalSectorDecomposition
      (K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
      (K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) marks)
    {S : Set (E × (ResidualHalfBandIndex K P D → ℝ))}
    (hS : IsConnected S) (hSrim : S ⊆ complementaryCutRim K P D hD hcofaces B h)
    (havoid : Disjoint S (complementaryBridgeCopies K P D hcofaces B h)) :
    ∃! i : Fin 4, Prod.fst '' S ⊆ C.rim i := by
  apply complementary_connected_gap_unique_original_rim K P D hD hcofaces B h
    hP hbound marks hmarks C hS
    (hSrim.trans (complementaryCut_rim_subset_carrier K P D hD hcofaces B h)) havoid
  apply (image_mono ?_).trans
    (complementaryCut_rim_without_bridges_projects_to_primalRim K P D hD hcofaces B h
      hP hbound hz)
  intro z hzS
  exact ⟨hSrim hzS, fun hzB ↦ Set.disjoint_left.mp havoid hzS hzB⟩

end PoincareConjecture.M76.OriginalTriangleCopies
